-- Prove2me | Theorems.Thm_DenardoDP_NStage_lemma2
-- name    : DenardoDP.NStage.lemma2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:59:59.563805+00:00
-- url     : https://prove2.me/theorems/5128f5d2-9cb5-42ba-8072-a27ad8135454
-- title:
--   Lemma 2 — Av ≤ v gives v ≥ f, Av ≥ v gives v ≤ f; Av_δ ≥ v_δ; H_δ v ≥ v gives v_δ ≥ H_δ v
-- statement:
--   Work in Denardo's model under the **monotonicity** and **N-stage contraction** assumptions, with $v_\delta$ the fixed point of $H_\delta^N$ for each policy $\delta$ and $f(x)=\sup_\delta v_\delta(x)$ the optimal return. Then:
--
--   1. (a) if $Av\le v$, then $v\ge f$; if $Av\ge v$, then $v\le f$;
--   2. (b) $Av_\delta\ge v_\delta$ for each $\delta\in\Delta$;
--   3. (c) if $H_\delta v\ge v$, then $v_\delta\ge H_\delta v$.
--
--   Inequalities between functions are pointwise. Part (a) says that $f$ is the smallest element of $V$ with $Av\le v$ and the largest with $Av\ge v$; it is the step that identifies $f$ as the fixed point of $A$ in Theorem 4 and makes $f$ optimal for the two mathematical programs of §6.
--
--   **Formalization Note** $f$ is any element of $V$ that is the pointwise least upper bound of $\{v_\delta(x)\}_\delta$ (such an $f$ exists by Theorem 4 (a)–(c)). The family $v$ satisfies $H_\delta^Nv_\delta=v_\delta$, the paper's definition of $v_\delta$ in §5.
-- source:
--   Denardo, Contraction Mappings in the Theory Underlying Dynamic Programming, SIAM Review 9(2) (1967), p. 169, Lemma 2 (proof pp. 169–170)

import Mathlib
import Definitions.Def_DenardoDP_NStage_Model

namespace DenardoDP.NStage

theorem lemma2 {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → DenardoDP.Contraction.BFun Ω → ℝ) (H : ((x : Ω) → D x) → DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω)
    (A : DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω) (v : ((x : Ω) → D x) → DenardoDP.Contraction.BFun Ω) (N : ℕ) (c : ℝ)
    (hH : DenardoDP.Contraction.IsPolicyOperator h H) (hA : DenardoDP.Contraction.IsMaxOperator h A)
    (hmono : DenardoDP.Contraction.MonotonicityAssumption H) (hN : NStageContractionAssumption H N c)
    (hv : ∀ δ, (H δ)^[N] (v δ) = v δ)
    (f : DenardoDP.Contraction.BFun Ω) (hf : DenardoDP.Contraction.IsOptimalReturn v f) :
    ((∀ w, DenardoDP.Contraction.PLe (A w) w → DenardoDP.Contraction.PLe f w) ∧ (∀ w, DenardoDP.Contraction.PLe w (A w) → DenardoDP.Contraction.PLe w f)) ∧
    (∀ δ, DenardoDP.Contraction.PLe (v δ) (A (v δ))) ∧
    (∀ δ w, DenardoDP.Contraction.PLe w (H δ w) → DenardoDP.Contraction.PLe (H δ w) (v δ)) := by sorry

end DenardoDP.NStage
