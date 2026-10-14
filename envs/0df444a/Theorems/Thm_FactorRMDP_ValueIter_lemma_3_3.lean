-- Prove2me | Theorems.Thm_FactorRMDP_ValueIter_lemma_3_3
-- name    : FactorRMDP.ValueIter.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:35.847802+00:00
-- url     : https://prove2.me/theorems/a78d4ad5-0da7-4b12-80e7-108d514050ef
-- title:
--   Lemma 3.3 — z(π) = max p₀ᵀ(r_π + λT_πβ) s.t. βᵢ ≤ min_{wᵢ∈𝒲ⁱ} wᵢᵀ(r_π + λT_πβ), attained at a fixed point
-- statement:
--   Consider a robust MDP whose factor matrix uncertainty set is r-rectangular, $\mathcal W = \mathcal W^1\times\cdots\times\mathcal W^r$, a discount factor $\lambda\in(0,1)$ and a stationary policy $\pi\in\Pi$. Then the policy evaluation problem can be reformulated as
--
--   $$z(\pi) = \max\Big\{ p_0^\top(r_\pi + \lambda T_\pi\beta) \;\Big|\; \beta\in\mathbb R^r,\ \beta_i \le \min_{w_i\in\mathcal W^i} w_i^\top(r_\pi+\lambda T_\pi\beta)\ \ \forall i\in[r]\Big\},$$
--
--   the maximum being attained. Moreover an optimal solution $\beta^\pi$ can be chosen such that for any $i\in[r]$,
--
--   $$\beta^\pi_i = \min_{w_i\in\mathcal W^i} w_i^\top\big(r_\pi + \lambda T_\pi\beta^\pi\big).$$
--
--   The reformulation turns the inner minimization over $\mathcal W$ into constraints that are linear in the decision maker's policy, which is what makes the min-max analysis of §4 possible.
--
--   **Formalization Note** The paper states the lemma "under Assumption 2.4" in a section devoted to r-rectangular sets; the proof (Appendix B, via (A.17)) uses r-rectangularity, and the reformulation fails without it (Appendix A example, pp. 22–23). We state it under r-rectangularity. The constraint uses $\varphi(\pi,\beta)_i$ of the definition file. The oracle part of Assumption 2.4 plays no role and is not formalized.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), p. 7, Lemma 3.3, (3.3)–(3.5); proof Appendix B, p. 23

import Mathlib
import Definitions.Def_FactorRMDP_ValueIter_Model

namespace FactorRMDP.ValueIter

open Matrix Filter Topology

/-- Lemma 3.3 (Goyal and Grand-Clément, arXiv:1811.00215v8, p. 7), under the standing assumption of
§3 that the uncertainty set is r-rectangular (Assumption 2.2). For `π ∈ Π`, `z(π)` is the maximum of
`p₀ᵀ(r_π + λ T_π β)` over `β ∈ ℝ^r` with `βᵢ ≤ min_{wᵢ ∈ 𝒲ⁱ} wᵢᵀ(r_π + λ T_π β)` for all `i`
((3.3)–(3.5)), and the maximum is attained at some `β^π` with
`β^π_i = min_{wᵢ ∈ 𝒲ⁱ} wᵢᵀ(r_π + λ T_π β^π)` for all `i`. -/
theorem lemma_3_3 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) (hR : M.IsRRect) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (π : S → A → ℝ) (hπ : π ∈ Policies S A) :
    IsGreatest {x | ∃ β : Fin r → ℝ, (∀ i, β i ≤ M.phi lam π β i) ∧
        x = M.p0 ⬝ᵥ (M.rpi π + lam • (M.T π *ᵥ β))} (M.z lam π) ∧
      ∃ β : Fin r → ℝ, (∀ i, β i = M.phi lam π β i) ∧
        M.p0 ⬝ᵥ (M.rpi π + lam • (M.T π *ᵥ β)) = M.z lam π := by sorry

end FactorRMDP.ValueIter
