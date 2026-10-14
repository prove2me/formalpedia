-- Prove2me | Theorems.Thm_CtxInvOpt_Greedy_lemma2_circumcenter_exists_unique
-- name    : CtxInvOpt.Greedy.lemma2_circumcenter_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:28.032218+00:00
-- url     : https://prove2.me/theorems/6c5459b7-9721-4269-a2f9-87c1577aca25
-- title:
--   Lemma 2, p. 12 — a circumcenter always exists, and it is unique when C ∖ {0} ≠ ∅ and α(C) < π/2
-- statement:
--   Let $d\ge2$ and let $C\subseteq\mathbb R^d$ be nonempty. Then there exists a **circumcenter** $\hat c(C)\in S^d$, i.e. a unit vector attaining the infimum in
--
--   $$\alpha(C)=\inf_{\hat c\in S^d}\sup_{c\in C}\theta(c,\hat c).$$
--
--   Furthermore, if $C\setminus\{0\}$ is nonempty and $\alpha(C)<\pi/2$, then the circumcenter is unique.
--
--   Existence makes the circumcenter policy well defined on every nonempty knowledge set; uniqueness is what pins down the greedy policy's proxy cost in the lower-bound construction of Theorem 2.
--
--   **Formalization Note** The angle uses the paper's convention $\theta(c,0)=\theta(0,\hat c)=0$. The standing assumption $d\ge2$ of §2 is a hypothesis. Uniqueness is stated as: any two circumcenters are equal.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 12, Lemma 2

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry

namespace CtxInvOpt.Greedy

/-- **Lemma 2 (Existence and uniqueness of circumcenter), arXiv:2106.14015v3, p. 12.** For every
nonempty `C ⊆ ℝ^d` there is a circumcenter `ĉ(C) ∈ S^d` attaining the infimum in (9); if moreover
`C \ {0}` is nonempty and `α(C) < π/2`, the circumcenter is unique. -/
theorem lemma2_circumcenter_exists_unique {d : ℕ} (hd : 2 ≤ d)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) :
    (∃ chat, CtxInvOpt.Offline.IsCircumcenter C chat) ∧
      ((C \ {0}).Nonempty → CtxInvOpt.Offline.uncAngle C < Real.pi / 2 →
        ∀ c₁ c₂, CtxInvOpt.Offline.IsCircumcenter C c₁ → CtxInvOpt.Offline.IsCircumcenter C c₂ → c₁ = c₂) := by sorry

end CtxInvOpt.Greedy
