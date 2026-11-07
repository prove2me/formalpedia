-- Prove2me | Theorems.Thm_CodeSW_lemma_7
-- name    : CodeSW.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:27:59.503899+00:00
-- url     : https://prove2.me/theorems/e3b0c761-1f25-4777-aab5-e726b2324361
-- title:
--   Lemma 7 — the Code SW chain converges to $\pi$ from every initial state, including zero temperature
-- statement:
--   **Correctness of Code Swendsen-Wang dynamics.** Let $P$ be the transition matrix of the Code Swendsen-Wang chain for a parity check matrix $h$. For every inverse temperature $\beta\ge0$ and all configurations $x_0,y$,
--   $$\lim_{T\to\infty}P^T(x_0,y)=\pi(y).$$
--   At zero temperature, where every satisfied check is kept ($p=1$), the chain converges from every $x_0$ to the zero-temperature Gibbs state, the uniform distribution on the code $\ker h$:
--   $$\lim_{T\to\infty}P^T(x_0,y)=\frac{\mathbf 1(y\in\ker h)}{2^{\dim\ker h}}.$$
--
--   This is the statement that the algorithm samples from the right distribution. It says nothing about the speed of convergence, which is the subject of the goal theorem.
--
--   Differences from the source:
--   - reading: Lemma 7 says the algorithm converges to π as T → ∞; the proof treats β < ∞ and then 'the case of zero temperature' (p.17) → two clauses: every real β ≥ 0, and the chain with p = 1 converging to the uniform law on ker h; reason: β = ∞ is not a real number, and the zero-temperature case is part of what the page proves
--   - encoding: convergence of the algorithm's output law → entrywise limit of the matrix power P^T(x₀, y); reason: the state space is finite, so the two agree
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Lemma 7, p.16, and its proof, pp.16–17

import Definitions.Def_CodeSW_cswKernel
open Matrix

namespace CodeSW

open Classical in
/-- **Lemma 7 (Correctness of Code SW dynamics).** The Code SW algorithm (Algorithm 2) converges
to `π` as `T → ∞` for any initial state `x₀`: for every inverse temperature `β ≥ 0`,
`P^T(x₀, y) → π(y)`; and at zero temperature (`p = 1`, every satisfied check is kept) the chain
converges to the zero-temperature Gibbs state, the uniform distribution on the code `ker h`
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, Lemma 7 and its proof, pp.16–17).

**Formalization Note** The zero-temperature case `β = ∞` is not a real `β`; it is the chain
`cswKernelP h 1`, and its limit `1(y ∈ ker h)/2^{dim ker h}` is the zero-temperature Gibbs state
(p.17). `kerA h univ` is `ker h`. -/
theorem lemma_7 {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) :
    (∀ β : ℝ, 0 ≤ β → ∀ x₀ y : Fin n → ZMod 2,
      Filter.Tendsto (fun T : ℕ => (cswKernel h β ^ T) x₀ y) Filter.atTop
        (nhds (gibbs h β y))) ∧
    (∀ x₀ y : Fin n → ZMod 2,
      Filter.Tendsto (fun T : ℕ => (cswKernelP h 1 ^ T) x₀ y) Filter.atTop
        (nhds (if y ∈ kerA h Finset.univ then ((2 : ℝ) ^ kDim h Finset.univ)⁻¹ else 0))) := by sorry

end CodeSW
