-- Prove2me | Theorems.Thm_DenardoDP_NStage_lemma1
-- name    : DenardoDP.NStage.lemma1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:59:28.457206+00:00
-- url     : https://prove2.me/theorems/d0fc8e32-f770-47ed-8aac-8af9072c033c
-- title:
--   Lemma 1 — under monotonicity, A is monotone, and A^n v and H_δ^n v increase from an improving start
-- statement:
--   Work in Denardo's model: a return $h$, the policy operators $H_\delta$ of (1) and the maximization operator $A$ of (3), both mapping the bounded functions $V$ into $V$. Write $u\ge v$ for the pointwise order. Suppose the **monotonicity assumption** holds: $u\ge v$ implies $H_\delta u\ge H_\delta v$ for every policy $\delta$. Then:
--
--   1. if $u\ge v$, then $Au\ge Av$;
--   2. if $Av\ge v$, then the sequence $(A^nv)_{n\ge0}$ is nondecreasing: $$A^{n+1}v\ge A^nv\quad\text{for every }n\ge0;$$
--   3. if $H_\delta v\ge v$, then the sequence $(H_\delta^nv)_{n\ge0}$ is nondecreasing: $H_\delta^{n+1}v\ge H_\delta^nv$ for every $n\ge0$.
--
--   Part 1 transfers monotonicity from the policy operators to the maximization operator; parts 2 and 3 are used in Lemma 2 and in the policy-improvement routine of §6.
--
--   **Formalization Note** The paper writes $\{v_n\}\uparrow$ for $v_n\ge v_{n-1}$ for each $n$; here it is stated as $A^{n+1}v\ge A^nv$ for every $n\in\mathbb N$, with $A^0v=v$. Only the monotonicity assumption is assumed, as in the paper; no contraction hypothesis is needed.
-- source:
--   Denardo, Contraction Mappings in the Theory Underlying Dynamic Programming, SIAM Review 9(2) (1967), p. 168, Lemma 1

import Mathlib
import Definitions.Def_DenardoDP_NStage_Model

namespace DenardoDP.NStage

theorem lemma1 {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → DenardoDP.Contraction.BFun Ω → ℝ) (H : ((x : Ω) → D x) → DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω)
    (A : DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω)
    (hH : DenardoDP.Contraction.IsPolicyOperator h H) (hA : DenardoDP.Contraction.IsMaxOperator h A)
    (hmono : DenardoDP.Contraction.MonotonicityAssumption H) :
    (∀ u w, DenardoDP.Contraction.PLe w u → DenardoDP.Contraction.PLe (A w) (A u)) ∧
    (∀ w, DenardoDP.Contraction.PLe w (A w) → ∀ n : ℕ, DenardoDP.Contraction.PLe (A^[n] w) (A^[n + 1] w)) ∧
    (∀ δ w, DenardoDP.Contraction.PLe w (H δ w) → ∀ n : ℕ, DenardoDP.Contraction.PLe ((H δ)^[n] w) ((H δ)^[n + 1] w)) := by sorry

end DenardoDP.NStage
