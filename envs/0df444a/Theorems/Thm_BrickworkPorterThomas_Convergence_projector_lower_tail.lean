-- Prove2me | Theorems.Thm_BrickworkPorterThomas_Convergence_projector_lower_tail
-- name    : BrickworkPorterThomas.Convergence.projector_lower_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:17:06.457683+00:00
-- url     : https://prove2.me/theorems/e042b936-69ef-470d-bb54-8610f61278bf
-- title:
--   Section 6, Eq. (128) — $\Pr[R_m<r_m/2d]\le 2^kk!/r_m^{k/2}$ from the design property
-- statement:
--   Let $U\sim\mathcal C(l)$ be a brickwork random circuit on $n$ qubits ($n$ even, $d=2^n$, depth at least one) whose law is a $d^{-k}$-approximate $k$-design for an even integer $k\ge2$. Factor $U=G_*C$ with $G_*$ a gate of the final layer and output pair $S_*$. Let $S=S_i$ be the contiguous interval obtained from $S_*$ by adding two preceding ring wires at each of $i$ steps, for $0\le i<M=n/2$, let $x$ be a fixed string on its complement, put $r=2^{|S|}$, and let $R_S=\sum_{z\in\{0,1\}^S}|\langle z,x_{\bar S}|C|0^n\rangle|^2$. Then
--
--   $$
--   \Pr\left[R_S<\frac{r}{2d}\right]\le\frac{2^kk!}{r^{k/2}} .
--   $$
--
--   The mass on a large set of qubits is thus unlikely to fall far below its Haar mean $r/d$. In the proof of Theorem 6.1 this is combined with the iterated two-gate bound, applied with $k=8$.
--
--   **Formalization Note** $x$ is a full bitstring whose entries on $S$ are ignored. The probability is over the gate configuration of the circuit.
--
--   Differences from the source:
--
--   - encoding: n even, qubits 1..n on a ring, d = 2^n → n = 2M with M ≥ 1, qubits Fin (2M) (0-based), d = 2^(2M); reason: Definition 2.4 assumes n even; every even n ≥ 2 is some 2M; relabelling only
--   - encoding: U ∼ C(l) with a final layer → U ∼ C(l+1), final layer index l (0-based); reason: the final gate exists only for depth ≥ 1; every depth ≥ 1 is l+1
--   - encoding: a law ν on SU(d) (Definition 2.3) → a law on d×d complex matrices supported on SU(d) (Borel σ-algebra of the matrix space); reason: the twirl and the output probability only depend on the pushed-forward law; same instances
--   - encoding: diamond norm of M_ν^(k) − M_μH^(k) on the k-fold system → the reused stabilized trace-norm diamond norm, after relabelling the basis of the k-fold system (k-tuples of bitstrings) by Fin(d^k); reason: a basis relabelling is a unitary permutation and changes no trace norm
--   - encoding: x a fixed string on the complement of S_i → x a full bitstring whose entries on S_i are ignored; reason: every complementary string arises and only its entries off S_i enter R_i
--   - encoding: the intervals S_i grow from the two-wire pair S* by two wires per step, ending at all n wires → S_i = expandedInterval M l p i, with i : Fin M and |S_i| = 2(i+1); reason: the stopping index is M−1; the source uses R_n and R_L for this terminal mass 1
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), §6, p. 19, Eq. (128) (proved in Eqs. (129)–(142), pp. 19–20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_BrickworkPorterThomas_Convergence_Circuit

namespace BrickworkPorterThomas.Convergence

open MeasureTheory

/-- Section 6, Eq. (128) (p. 19). Let `U = G_* C ∼ C(l+1)` on `n = 2M` qubits be a
`d^{-k}`-approximate `k`-design for an even `k ≥ 2`, let `S` be a set of qubits containing the
output pair `S_*` of the final gate `G_*`, `S = S_i` the actual enlarging interval,
`x` a fixed string off `S`, `r = 2^{|S|}`, and
`R_S = Σ_{z ∈ {0,1}^S} |⟨z, x_{\bar S}|C|0^n⟩|²`. Then `Pr[R_S < r/(2d)] ≤ 2^k k! / r^{k/2}`. -/
theorem projector_lower_tail (M l k : ℕ) (p i : Fin M)
    (x : Bits (2 * M)) (hM : 1 ≤ M) (hk : 2 ≤ k) (hkeven : Even k)
    (hdesign : IsApproxDesign (circuitLaw M (l + 1)) k (designTol M k)) :
    let S := expandedInterval M l p i
    gateLaw M (l + 1)
        {g | marginalMass p S x g < (2 : ℝ) ^ S.card / (2 * (2 : ℝ) ^ (2 * M))} ≤
      ENNReal.ofReal ((2 : ℝ) ^ k * k.factorial / ((2 : ℝ) ^ S.card) ^ (k / 2)) := by sorry

end BrickworkPorterThomas.Convergence
