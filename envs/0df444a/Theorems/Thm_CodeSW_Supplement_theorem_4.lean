-- Prove2me | Theorems.Thm_CodeSW_Supplement_theorem_4
-- name    : CodeSW.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:50:26.741606+00:00
-- url     : https://prove2.me/theorems/b2ff411e-9ab7-4dee-9d11-f269a67e884f
-- title:
--   Theorem 4 — Algorithm 1 converges to the Gibbs state $e^{-\beta H}/\operatorname{tr}e^{-\beta H}$
-- statement:
--   Let $g\in\{0,1\}^{c\times 2n}$ be a stabilizer matrix, $h=g\omega$ the associated classical parity check matrix, $\beta\in\mathbb R$, and $\pi(x)\propto e^{-2\beta|hx|}$ the Gibbs distribution of $h$ on $\{0,1\}^{2n}$. Let $Q$ be a transition matrix on $\{0,1\}^{2n}$ that is irreducible, aperiodic and reversible with respect to $\pi$, and invariant under logical shifts:
--   $$Q(x,y)=Q(x,y+\ell)\qquad\text{for all }x,y\text{ and every }\ell\in\ker h.\tag{8}$$
--   Fix preimages $e_s$ with $he_s=s$ for every syndrome $s\in S_g$, an initial classical state $x_0$ and an initial unit vector $|\phi_0\rangle$. Then the averaged output $\rho_T=\mathbb E_\phi|\phi\rangle\langle\phi|$ of Algorithm 1 after $T$ iterations satisfies
--   $$\lim_{T\to\infty}\rho_T=\frac{e^{-\beta H}}{\operatorname{tr}e^{-\beta H}},\qquad H=-\sum_{i\in[c]}P(g_i).$$
--
--   The theorem reduces quantum Gibbs state preparation for stabilizer Hamiltonians to classical sampling from the Gibbs distribution of the code $h=g\omega$: any classical chain with the logical-shift invariance (8), such as the Code Swendsen-Wang chain, can be lifted to a quantum sampler.
--
--   **Formalization Note** Convergence is in the finite-dimensional space of complex matrices. $\rho_T$ is the exact average over all measurement outcomes and classical samples, not a single trajectory and not a time average.
--
--   Differences from the source:
--   - reading: Q(x,y) = Q(x,y+ℓ) for any ℓ representing a logical operator, i.e. P(ℓ) ∈ L (eq. (8)) → Q x y = Q x (y + ℓ) for every ℓ with (gω)ℓ = 0; reason: L = C/S is a quotient of the commutant C = P(ker h) (p.10), so the strings representing its elements are the ℓ ∈ ker h; Lemma 8's proof (p.18) treats them as this subspace
--   - reading: lim_{T→∞} E_ϕ |ϕ⟩⟨ϕ| ∝ e^{−βH} → ρ_T tends to e^{−βH} / tr e^{−βH}; reason: every ρ_T has trace one, so a limit proportional to e^{−βH} is its trace normalization
--   - generalization: E(s) = P(e_s) with e_s the lexicographically first preimage of s under h → E(s) = P(e s) for every choice function e with h(e s) = s on S_g; reason: the lexicographic choice is one such e, so the Lean statement specializes to the page's
--   - generalization: β an inverse temperature → every real β; reason: specializes to every positive β; the Gibbs law and state are defined for every real β
--   - encoding: g the stabilizer matrix of a stabilizer code (commuting Paulis, stabilizer group S) → IsStabilizerMatrix g: pairwise commuting P(g_i) and a nonzero common +1 eigenvector; reason: for commuting Hermitian Paulis a nonzero code space is equivalent to −I ∉ S, which the page's code-space projector presupposes
--   - encoding: E_ϕ |ϕ⟩⟨ϕ|, the average over the outputs sampled from Algorithm 1 → alg1Output: ∑_x σ_T(x) for the exact recursion σ_t of the classical–quantum law; reason: the recursion is the exact law of the algorithm's measurement outcomes and classical samples
--   - encoding: (ℂ²)^{⊗n}, strings in {0,1}^{2n}, Π(g,s) = E(s)Π(g,0)E(s) → functions on Fin n → ZMod 2; Fin (n + n) → ZMod 2; Π(g,s) = ∏_i (1 + (−1)^{s_i}P(g_i))/2; reason: Lean conventions; for a stabilizer matrix the product formula is the same projector
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Theorem 4, p.12; hypotheses on Q and eq. (8), p.12; Algorithm 1, p.12; §2.1.1, pp.10–11

import Definitions.Def_CodeSW_Supplement_alg1State
import Definitions.Def_mm_basic

set_option autoImplicit false

open Matrix Filter Topology

namespace CodeSW.Supplement

/-- **Theorem 4 (Convergence to the Gibbs state).** Let `g ∈ {0,1}^{c×2n}` be a stabilizer matrix,
`h = gω`, `β ∈ ℝ`, and `π` the Gibbs distribution of `h` at `β` on `{0,1}^{2n}`. Let `Q` be a
transition matrix on `{0,1}^{2n}` that is irreducible, aperiodic and reversible with respect to
`π`, and satisfies eq. (8): `Q(x,y) = Q(x,y+ℓ)` for all `x, y` and every `ℓ ∈ ker h`. Then for every
choice of syndrome representatives `e_s` (`h e_s = s`), every initial classical state `x₀` and every
initial unit vector `|ϕ₀⟩`, the averaged output `ρ_T = E_ϕ |ϕ⟩⟨ϕ|` of Algorithm 1 converges, as
`T → ∞`, to the Gibbs state `e^{−βH}/tr e^{−βH}` of `H = −∑_i P(g_i)`
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, Theorem 4, p.12; hypotheses on `Q`: p.12, eq. (8)).

**Formalization Note** "`P(ℓ) ∈ L`" in (8) is read as `ℓ ∈ ker h`, i.e. `P(ℓ)` in the commutant
`C = P(ker h)` whose classes form `L = C/S` (p.10). The page's `lim ∝ e^{−βH}` is stated as
convergence to the trace-normalized `e^{−βH}`. The theorem holds for every real `β` and every choice
of `e`; the page's `e_s` is the lexicographically first preimage. -/
theorem theorem_4 {n c : ℕ} (g : Matrix (Fin c) (Fin (n + n)) (ZMod 2))
    (hg : IsStabilizerMatrix g) (β : ℝ)
    (Q : Matrix (Fin (n + n) → ZMod 2) (Fin (n + n) → ZMod 2) ℝ)
    (hQs : MarkovMixing.IsStochastic Q) (hQi : MarkovMixing.Irreducible Q)
    (hQa : MarkovMixing.Aperiodic Q)
    (hQr : MarkovMixing.DetailedBalance Q (CodeSW.gibbs (checkMatrix g) β))
    (hQ8 : ∀ x y ℓ : Fin (n + n) → ZMod 2, checkMatrix g *ᵥ ℓ = 0 → Q x y = Q x (y + ℓ))
    (e : (Fin c → ZMod 2) → (Fin (n + n) → ZMod 2))
    (he : ∀ s ∈ syndromes g, checkMatrix g *ᵥ e s = s)
    (x₀ : Fin (n + n) → ZMod 2) (ϕ₀ : (Fin n → ZMod 2) → ℂ) (hϕ₀ : star ϕ₀ ⬝ᵥ ϕ₀ = 1) :
    Tendsto (fun T : ℕ => alg1Output g Q e x₀ ϕ₀ T) atTop (𝓝 (quantumGibbs g β)) := by sorry

end CodeSW.Supplement
