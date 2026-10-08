-- Prove2me | Theorems.Thm_AffinePolicies_GeneralApprox_lemma_12
-- name    : AffinePolicies.GeneralApprox.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:25:18.257647+00:00
-- url     : https://prove2.me/theorems/677e31bf-fdae-447c-816a-31886b3e485a
-- title:
--   Lemma 12, PDF p. 35 — 𝒰⁰ dominates 𝒰
-- statement:
--   Let $\mathcal U\subseteq\mathbb R^m_+$ have nonempty interior. For $j=1,\dots,m$ let $\mu_j=\max\{b_j: b\in\mathcal U\}$ and let $\beta^j\in\mathcal U$ attain it, $\beta^j_j=\mu_j$, as in (38). Let $u^1,\dots,u^K$ be a complete run of Algorithm $\mathcal A$ on $\mathcal U$ with output $\beta=u^1+\dots+u^K$, and let
--   $$\mathcal U^0=\operatorname{conv}\{2\sqrt m\cdot\beta^1,\dots,2\sqrt m\cdot\beta^m,\ 2\beta\}$$
--   be the set (66). Then $\mathcal U^0$ dominates $\mathcal U$:
--   $$\forall b\in\mathcal U\quad \exists b'\in\mathcal U^0:\quad b\le b'.$$
--
--   Domination is what lets a solution designed for $\mathcal U^0$, a polytope with at most $m+1$ vertices, be used for every scenario of the original set $\mathcal U$.
--
--   **Formalization Note** The statement holds for every run of Algorithm $\mathcal A$ and every choice of the maximizers $\beta^j$. Compactness and convexity of $\mathcal U$ and the model data of (1) are not used by the claim and are omitted; $\mu$ is given through its defining property, and $\mu_j>0$ follows from full-dimensionality.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Lemma 12, PDF p. 35

import Mathlib
import Definitions.Def_AffinePolicies_GeneralApprox_Setting

namespace AffinePolicies.GeneralApprox

open Matrix

/-- Lemma 12 (PDF p. 35): the set 𝒰⁰ of (66), built from the argmax points βʲ of (38) and the
output β of a run of Algorithm 𝒜, dominates 𝒰: every b ∈ 𝒰 lies below some b' ∈ 𝒰⁰. -/
theorem lemma_12 {m : ℕ} (U : Set (Fin m → ℝ))
    (hUnn : ∀ b ∈ U, 0 ≤ b) (hUfull : (interior U).Nonempty)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : AffinePolicies.SqrtBound.IsRun U μ K u) :
    ∀ b ∈ U, ∃ b' ∈ U0 bstar u K, b ≤ b' := by sorry

end AffinePolicies.GeneralApprox
