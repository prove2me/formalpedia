-- Prove2me | Theorems.Thm_DRConvexOpt_InfConv_limit_display
-- name    : DRConvexOpt.InfConv.limit_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:43.489039+00:00
-- url     : https://prove2.me/theorems/49519e22-bc67-404a-82d9-84ae81801c3e
-- title:
--   Proof of Theorem 3, p. 37 — with δ_{j⋆}(k) = 1 − 1/k and δ_j(k) = 1/(k(J−1)), the sum Σ δ_j(k) sup_{𝒫^j} E[v(y_j/δ_j(k))] → sup_{𝒫^{j⋆}} E[v(x)]
-- statement:
--   Let $\mathcal P$ be the standardized ambiguity set satisfying (C2), $\{\mathcal I_j\}_{j\in\mathcal J}$ a partition with $J = |\mathcal J| \ge 2$ blocks and outer approximations $\mathcal P^j$, and $v$ as in (C3). Assume the **uniform first-moment bound**: for each $j$ there is $M_j$ with $\mathbb E_{\mathbb P}\|\tilde z\| \le M_j$ for all $\mathbb P \in \mathcal P^j$. Fix $x \in \mathbb R^N$ and $j^\star \in \mathcal J$, and for $k \ge 2$ set
--   $$y_{j^\star} = x,\quad \delta_{j^\star}(k) = 1 - \tfrac1k,\qquad y_j = 0,\quad \delta_j(k) = \tfrac{1}{k(J-1)}\ \ (j \ne j^\star).$$
--   Then:
--   1. $(y,\delta(k)) \in \Gamma(x)$ for every $k \ge 2$;
--   2. as $k \to \infty$,
--   $$\sum_{j\in\mathcal J}\delta_j(k)\sup_{\mathbb P\in\mathcal P^j}\mathbb E_{\mathbb P}[v(y_j/\delta_j(k),\tilde z)] \longrightarrow \sup_{\mathbb P\in\mathcal P^{j^\star}}\mathbb E_{\mathbb P}[v(x,\tilde z)].$$
--
--   This limiting argument is the paper's route from (6) to (7): the constraint $\delta > 0$ of $\Gamma(x)$ prevents putting all weight on the minimizing block $j^\star$.
--
--   **Formalization Note** The paper justifies the limit by "$\sup_{\mathbb P\in\mathcal P^j}\mathbb E_{\mathbb P}[v(0,\tilde z)]$ is finite for all $j$", which does not follow from (C1)–(C3) and (N′): $\mathcal P^j$ drops the support condition of $\mathcal C_I$ when $I \notin \mathcal I_j$. The uniform first-moment bound is an **added, disclosed hypothesis**; it gives that finiteness and also the uniform convergence of $\delta\, v(x/\delta, z)$ to $v(x,z)$. Condition (C2) is used only to make $\mathcal P$, hence every $\mathcal P^j$, nonempty. The convergence is in `EReal`; the index $k$ is a natural number, and the values of $\delta(k)$ for $k < 2$ are irrelevant to the limit. $J - 1$ is computed in $\mathbb R$.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 37, proof of Theorem 3, second paragraph (limiting display)

import Mathlib
import Definitions.Def_DRConvexOpt_InfConv_Setting

namespace DRConvexOpt.InfConv

open MeasureTheory Matrix Filter Topology

/-- Proof of Theorem 3, p. 37, the limiting display: for `J ≥ 2` and any `j⋆ ∈ 𝒥`, put
`y_{j⋆} = x`, `δ_{j⋆}(k) = 1 − 1/k`, and `y_j = 0`, `δ_j(k) = 1/(k(J − 1))` for `j ≠ j⋆`. Then
`(y, δ(k)) ∈ Γ(x)` for every `k ≥ 2`, and
`∑_j δ_j(k) sup_{𝒫^j} E[v(y_j/δ_j(k), z̃)] → sup_{𝒫^{j⋆}} E[v(x, z̃)]` as `k → ∞`.
The paper's justification "sup_{𝒫^j} E[v(0, z̃)] is finite for all j" is replaced by the disclosed
assumption `UnifFirstMoment`; (C2) makes 𝒫, hence every 𝒫^j, nonempty. -/
theorem limit_display {nP nQ nK nI nN nL nJ : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL) (blk : Fin (nI + 1) → Fin nJ)
    (hC2 : ∃ μ ∈ ambiguitySet d, ∀ i, d.plo i < d.phi i →
      μ.real (d.conf i) ∈ Set.Ioo (d.plo i) (d.phi i))
    (hFM : UnifFirstMoment d blk) (hJ : 2 ≤ nJ) (jstar : Fin nJ) (x : Fin nN → ℝ) :
    let δk : ℕ → Fin nJ → ℝ := fun k j =>
      if j = jstar then 1 - 1 / (k : ℝ) else 1 / ((k : ℝ) * ((nJ : ℝ) - 1))
    let yk : Fin nJ → Fin nN → ℝ := fun j => if j = jstar then x else 0
    (∀ k : ℕ, 2 ≤ k → (yk, δk k) ∈ Gamma x) ∧
      Tendsto (fun k : ℕ => ∑ j, ((δk k j : ℝ) : EReal) *
          worstCase (outerSet d blk j) (fun ω => v.eval ((δk k j)⁻¹ • yk j) ω.1)) atTop
        (𝓝 (worstCase (outerSet d blk jstar) (fun ω => v.eval x ω.1))) := by sorry

end DRConvexOpt.InfConv
