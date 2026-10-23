-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_eq_49_50
-- name    : CTJMDP.MarkovSuff.eq_49_50
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:25.203119+00:00
-- url     : https://prove2.me/theorems/ff981a48-0461-47ce-93e7-5e16d01f3fce
-- title:
--   (49)–(50), p. 13 — 𝔼^π_x f(ξ_s,π_s)I{ξ_s∈Z} = ∫_Z f(z,ϕ_s)P^π_x(s,dz), and its time integral, when ϕ satisfies (16)
-- statement:
--   Throughout, $X$ and $A$ are standard Borel spaces, $A(x)\subseteq A$ are the feasible action sets, $\tilde q$ are the transition rates of the CTJMDP, the standing assumptions (i)–(iv) of §2 hold, and Assumption 2.1 holds: $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x\in X$.
--
--   Let $x\in X$, let $\pi$ be a policy with law $\mathbb P^\pi_x$, and let $\phi$ be a Markov policy satisfying (16) for $(\delta_x,\pi)$. Let $f\ge0$ be measurable on $X\times A$ and write $f(z,p)=\int f(z,a)\,p(da)$, (3). Then, for every measurable $Z$,
--   $$\mathbb E^\pi_xf(\xi_s,\pi_s)I\{\xi_s\in Z\}=\int_Zf(z,\phi_s)\,P^\pi_x(s,dz),\qquad s>0,\qquad(49)$$
--   and, for every $t>0$,
--   $$\mathbb E^\pi_x\Big(\int_0^tf(\xi_s,\pi_s)I\{\xi_s\in Z\}\,ds\Big)=\int_0^t\mathbb E^\pi_xf(\xi_s,\pi_s)I\{\xi_s\in Z\}\,ds=\int_0^t\!\int_Zf(z,\phi_s)\,P^\pi_x(s,dz)\,ds.\qquad(50)$$
--
--   Applied to $f(z,a)=\tilde q(z,a,Z\setminus\{z\})$ and $f(z,a)=\tilde q(z,a)$, (50) turns the expectations in (37) into the integrals of (32) for $\phi$; this is how Lemma 2(i) follows from Lemma 4.
--
--   **Formalization Note** The process is read at $\xi_{s-}$, which equals $\xi_s$ almost surely for each fixed $s$ and for almost every $s$ along each path.
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, pp. 13, proof of Lemma 2, (49)–(50)

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- (49)–(50) (pp. 13–14, proof of Lemma 2). -/
theorem eq_49_50 {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (x : X) (π : Policy X A) (hπ : IsPolicy M π)
    (phi : X → ℝ → Measure A) (hphi : IsMarkovPolicy M phi)
    (P : Measure (Traj X)) (hP : IsLaw M (Measure.dirac x) π P)
    (h16 : Disintegrates P π phi)
    (f : X → A → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (Z : Set X) (hZ : MeasurableSet Z) :
    (∀ s : ℝ, 0 < s →
      expAt P π s (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ a, f z a ∂p) =
        ∫⁻ z in Z, (∫⁻ a, f z a ∂(phi z s)) ∂(stateMarg P s)) ∧
    (∀ t : ℝ, 0 < t →
      expPath P π t (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ a, f z a ∂p) =
        ∫⁻ s in Ioc (0 : ℝ) t,
          expAt P π s (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ a, f z a ∂p) ∧
      ∫⁻ s in Ioc (0 : ℝ) t,
          expAt P π s (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ a, f z a ∂p) =
        ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ z in Z, (∫⁻ a, f z a ∂(phi z s)) ∂(stateMarg P s)) := by sorry

end CTJMDP.MarkovSuff
