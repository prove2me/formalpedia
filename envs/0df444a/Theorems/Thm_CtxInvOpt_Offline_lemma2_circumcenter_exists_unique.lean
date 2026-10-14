-- Prove2me | Theorems.Thm_CtxInvOpt_Offline_lemma2_circumcenter_exists_unique
-- name    : CtxInvOpt.Offline.lemma2_circumcenter_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:47.055801+00:00
-- url     : https://prove2.me/theorems/ba73b37a-6e36-4a6b-841b-0e170dc3fb8c
-- title:
--   Lemma 2, p. 12 — every nonempty C has a circumcenter, unique when C ∖ {0} ≠ ∅ and α(C) < π/2
-- statement:
--   Let $d\ge2$ and let $C\subseteq\mathbb R^d$ be nonempty. Recall the uncertainty angle
--   $$\alpha(C)=\inf_{\hat c\in S^d}\sup_{c\in C}\theta(c,\hat c).$$
--   Then:
--
--   1. there exists a circumcenter of $C$, i.e. a vector $\hat c(C)\in S^d$ with $\sup_{c\in C}\theta(c,\hat c(C))=\alpha(C)$;
--   2. if moreover $C\setminus\{0\}$ is nonempty and $\alpha(C)<\pi/2$, then the circumcenter is unique.
--
--   The lemma makes the circumcenter policy of Theorem 1 well defined: the minimizer it uses always exists, and in the regime where the knowledge set fits in an open half-space it is uniquely determined.
--
--   **Formalization Note** $C$ is an arbitrary nonempty subset of $\mathbb R^d$, not necessarily of the sphere, as in the paper. The angle convention $\theta(0,\hat c)=0$ means that the zero vector never affects $\alpha(C)$. The hypothesis $d\ge2$ is the paper's standing assumption.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 12, Lemma 2; proof App-5–App-7

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry

namespace CtxInvOpt.Offline

/-- **Lemma 2 (Existence and uniqueness of circumcenter), arXiv:2106.14015v3, p. 12.** For every
nonempty `C ⊆ ℝ^d` there is a circumcenter `ĉ(C) ∈ S^d` attaining the infimum in (9); if moreover
`C \ {0}` is nonempty and `α(C) < π/2`, the circumcenter is unique. -/
theorem lemma2_circumcenter_exists_unique {d : ℕ} (hd : 2 ≤ d)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) :
    (∃ chat, IsCircumcenter C chat) ∧
      ((C \ {0}).Nonempty → uncAngle C < Real.pi / 2 →
        ∀ c₁ c₂, IsCircumcenter C c₁ → IsCircumcenter C c₂ → c₁ = c₂) := by sorry

end CtxInvOpt.Offline
