-- Prove2me | Theorems.Thm_BrickworkPorterThomas_Convergence_two_gate_bound
-- name    : BrickworkPorterThomas.Convergence.two_gate_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:19:32.5912+00:00
-- url     : https://prove2.me/theorems/4b51811c-e8c3-468d-bd10-b96754c18638
-- title:
--   Lemma A.2 — two Haar gates: $E[\varphi(P_\rho)]\le E[\varphi(B_1B_2)]$, $B_i\sim\mathrm{Beta}(2,2)$
-- statement:
--   Let $q_1,q_2,q_3$ be three consecutive qubits, and let $G,H$ be independent Haar random two-qubit gates in $\mathrm{SU}(4)$, with $G$ acting first on $(q_2,q_3)$ and $H$ then on $(q_1,q_2)$. Fix $x_1,x_2\in\{0,1\}$ and a density operator $\rho$ on the three qubits (positive semidefinite, trace one), and define
--
--   $$
--   P_\rho=\mathrm{Tr}\left[(|x_1x_2\rangle\langle x_1x_2|\otimes I_3)\,HG\rho G^\dagger H^\dagger\right].
--   $$
--
--   Then for every bounded convex function $\varphi:[0,1]\to\mathbb R$,
--
--   $$
--   \mathbb E_{G,H}[\varphi(P_\rho)]\le\mathbb E_{B_1,B_2}[\varphi(B_1B_2)],\qquad B_1,B_2\overset{\text{i.i.d.}}{\sim}\mathrm{Beta}(2,2),
--   $$
--
--   where $\mathrm{Beta}(2,2)$ has density $6p(1-p)$ on $[0,1]$.
--
--   This convex-order comparison controls how the marginal probability mass grows when an interval of qubits is enlarged by two through the last two layers. It is the step that is iterated in the proof of Theorem 6.1.
--
--   **Formalization Note** $\varphi$ is a real function on $\mathbb R$ that is convex and bounded on $[0,1]$. Only its values on $[0,1]$ enter, since $P_\rho$ and $B_1B_2$ take values there. $\mathrm{Beta}(2,2)$ is Mathlib's `betaMeasure 2 2`.
--
--   Differences from the source:
--
--   - encoding: φ : [0,1] → ℝ bounded convex → φ : ℝ → ℝ, convex on [0,1] and bounded there; reason: only values on [0,1] enter; every function on [0,1] extends
--   - encoding: three consecutive qubits of a circuit and a state ρ on them → a three-qubit register Fin 3 = (q₁, q₂, q₃) and a 3-qubit density matrix ρ; reason: P_ρ only involves these three qubits
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), Appendix A, p. 23, Lemma A.2, Eqs. (163)–(164); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_BrickworkPorterThomas_Convergence_Circuit

open scoped ComplexOrder

namespace BrickworkPorterThomas.Convergence

open MeasureTheory

/-- Lemma A.2 (p. 23). Let `G, H` be independent Haar random gates in `SU(4)`, `G` acting first on
`(q₂, q₃)` and `H` then on `(q₁, q₂)` of three consecutive qubits, fix `x₁, x₂ ∈ {0,1}` and a
three-qubit density operator `ρ`, and let `P_ρ = Tr[(|x₁x₂⟩⟨x₁x₂| ⊗ I₃) H G ρ G† H†]`. Then for
every bounded convex `φ : [0,1] → ℝ`, `E_{G,H}[φ(P_ρ)] ≤ E[φ(B₁ B₂)]` with `B₁, B₂` independent
`Beta(2,2)` (density `6p(1−p)` on `[0,1]`). -/
theorem two_gate_bound (x₁ x₂ : Fin 2) (ρ : QMat 3) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Set.Icc 0 1) φ)
    (hbdd : ∃ B : ℝ, ∀ p ∈ Set.Icc (0 : ℝ) 1, |φ p| ≤ B) :
    ∫ GH : SU4 × SU4, φ (twoGateProb x₁ x₂ ρ GH.1 GH.2) ∂((haarSU (Bits 2)).prod (haarSU (Bits 2))) ≤
      ∫ B : ℝ × ℝ, φ (B.1 * B.2)
        ∂((ProbabilityTheory.betaMeasure 2 2).prod (ProbabilityTheory.betaMeasure 2 2)) := by sorry

end BrickworkPorterThomas.Convergence
