-- Prove2me | Theorems.Thm_BealeConvexMin_SumLargest_descent_rules
-- name    : BealeConvexMin.SumLargest.descent_rules
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:38:48.944159+00:00
-- url     : https://prove2.me/theorems/63abd4c0-01d1-4ecc-973b-994b7ebdcff3
-- title:
--   Theorem 1 (a), second half, p. 179 — the six descent rules when (4.5) fails
-- statement:
--   In the setting of Theorem 1 (a) of Beale's paper, with $\tau\le s$, write $a_l=A_l+\tau c_{0l}$ and $w_f=\varphi_f+\tau\theta_f$, and let $F$ be the set of free $z_l$. Each of the following moves, with every other variable held at zero, makes $C$ strictly smaller than $C(0,0)$ for all sufficiently small step sizes $t>0$:
--
--   1. if $a_l<0$: set $z_l=t$ (increase $z_l$ from zero);
--   2. if $a_l>0$ and $z_l$ is free: set $z_l=-t$ (decrease $z_l$ from zero);
--   3. if $w_f<0$: set $u_f=t$;
--   4. if $w_f>1$: set $u_f=-t$;
--   5. if $\sum_{f=1}^{s}w_f<\tau-1$: set $u_1=\dots=u_s=t$;
--   6. if $\sum_{f=1}^{s}w_f>\tau$: set $u_1=\dots=u_s=-t$.
--
--   Formally, in each case there is $\varepsilon>0$ such that for all $0<t<\varepsilon$
--   $$C(\text{moved point})<C(0,0).$$
--
--   Each rule shows that the corresponding condition of (4.5) is necessary for the origin to be a minimum; the rules are also the pivoting instructions of Beale's simplex-type algorithm for this objective.
--
--   **Formalization Note** "$C$ can be decreased" is read as a strict decrease for all small moves along the stated direction. The paper's $f=1,\dots,s$ are Lean's $0,\dots,s-1$; "$z_l$ free" is $l\in F$.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 179 (PDF p. 7), Theorem 1 (a), second half ("If these conditions are not all satisfied, C can be decreased as follows")

import Mathlib
import Definitions.Def_BealeConvexMin_SumLargest_sumLargest
import Definitions.Def_BealeConvexMin_SumLargest_Forms

namespace BealeConvexMin.SumLargest

/-- Beale (1955), Theorem 1 (a), second half, p. 179: "If these conditions are not all satisfied,
`C` can be decreased as follows". Each rule moves one coordinate (or all `u_f` equally) away from
zero, every other variable staying at zero, and `C` then drops strictly below `C(0, 0)` for all
small enough moves. `F` is the set of `l` with `z_l` free. -/
theorem descent_rules {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ ≤ s) (F : Finset (Fin r)) :
    -- If `A_l + τ c_0l < 0`, increase `z_l` from zero.
    (∀ l : Fin r, P.A l + (τ : ℝ) * P.c0 l < 0 →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ (Pi.single l t) 0 < P.C τ 0 0) ∧
    -- If `A_l + τ c_0l > 0`, decrease `z_l` from zero if it is free.
    (∀ l ∈ F, 0 < P.A l + (τ : ℝ) * P.c0 l →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ (Pi.single l (-t)) 0 < P.C τ 0 0) ∧
    -- If `φ_f + τ θ_f < 0`, increase `u_f` from zero.
    (∀ f : Fin s, P.φ f + (τ : ℝ) * P.θ f < 0 →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ 0 (Pi.single f t) < P.C τ 0 0) ∧
    -- If `φ_f + τ θ_f > 1`, decrease `u_f` from zero.
    (∀ f : Fin s, 1 < P.φ f + (τ : ℝ) * P.θ f →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ 0 (Pi.single f (-t)) < P.C τ 0 0) ∧
    -- If `Σ_f (φ_f + τ θ_f) < τ - 1`, increase `u_1, …, u_s` equally from zero.
    (∑ f, (P.φ f + (τ : ℝ) * P.θ f) < (τ : ℝ) - 1 →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ 0 (fun _ => t) < P.C τ 0 0) ∧
    -- If `Σ_f (φ_f + τ θ_f) > τ`, decrease `u_1, …, u_s` equally from zero.
    ((τ : ℝ) < ∑ f, (P.φ f + (τ : ℝ) * P.θ f) →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ 0 (fun _ => -t) < P.C τ 0 0) := by sorry

end BealeConvexMin.SumLargest
