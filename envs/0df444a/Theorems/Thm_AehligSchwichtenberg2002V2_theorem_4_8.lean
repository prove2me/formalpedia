-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002V2_theorem_4_8
-- name    : AehligSchwichtenberg2002V2.theorem_4_8
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T06:58:06.81339+00:00
-- url     : https://prove2.me/theorems/8f793c17-e1b1-4aa8-9ab4-06907a36cc9a
-- title:
--   Theorem 4.8 — Strict decrease and the reduction-chain bound
-- statement:
--   For a typed term $t$ and $N\ge|\operatorname{FV}(t)|$, each reduction step strictly decreases $\vartheta(t)(N)+|t|$. A reduction sequence starting at $t$ has length at most this measure evaluated at $N=|\operatorname{FV}(t)|$.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg (2002), A syntactical analysis of non-size-increasing polynomial time computation, Theorem 4.8. https://arxiv.org/abs/cs/0011037

import Definitions.Def_AehligSchwichtenberg2002V2_Bounds

namespace AehligSchwichtenberg2002V2

theorem theorem_4_8 {Γ : Context} {t : Term} {τ : Ty}
    (ht : HasType Γ t τ) :
    (∀ (N : Nat) (t' : Term),
      freeVarCard t ≤ N → RedStep t t' → stepMeasure t' N < stepMeasure t N) ∧
    (∀ (k : Nat) (t' : Term),
      RedSteps k t t' → k ≤ stepMeasure t (freeVarCard t)) := by sorry

end AehligSchwichtenberg2002V2
