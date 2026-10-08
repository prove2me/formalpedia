-- Prove2me | Theorems.Thm_DenardoDP_NStage_theorem4
-- name    : DenardoDP.NStage.theorem4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:59:12.172929+00:00
-- url     : https://prove2.me/theorems/65127aac-bfd6-4155-aa84-a86814791aeb
-- title:
--   Theorem 4 — under monotonicity and N-stage contraction, f is the unique fixed point of E and of A, and ρ(A^N v, f) ≤ cρ(v, f) for v ≤ f
-- statement:
--   Let $\Omega$ be a set, $D_x$ a decision set at each $x\in\Omega$, $\Delta=\times_xD_x$ the policies, $V$ the bounded real functions on $\Omega$ with the sup metric $\rho$, $h(x,d_x,v)$ the return, $H_\delta$ the policy operators $[H_\delta v](x)=h(x,\delta_x,v)$ and $A$ the maximization operator $(Av)(x)=\sup_{d_x\in D_x}h(x,d_x,v)$, both mapping $V$ into $V$. Suppose:
--
--   - the **monotonicity assumption**: $u\ge v$ implies $H_\delta u\ge H_\delta v$ for every $\delta$;
--   - the **N-stage contraction assumption**: for a positive integer $N$ and $c<1$, independent of $\delta$, each $H_\delta^N$ has modulus $c$ or less and each $H_\delta$ has modulus $1$ or less.
--
--   Let $v_\delta$ be the fixed point of $H_\delta^N$, let $E$ be the operator $(Ev)(x)=\sup_\delta(H_\delta^Nv)(x)$, and let $f(x)=\sup_\delta v_\delta(x)$ be the optimal return. Then:
--
--   1. (a) $v_\delta$ is the unique fixed point of $H_\delta$;
--   2. (b) $\rho(v_\delta,v)\le\rho(H_\delta v,v)\,N/(1-c)$ for every $v\in V$;
--   3. (c) $E$ is a contraction mapping of modulus $c$ or less;
--   4. (d) $f\in V$, and $f$ is the unique fixed point of $E$ and the unique fixed point of $A$: $$Ef=f,\qquad Af=f;$$
--   5. (e) if $v\le f$, then $$\rho(A^Nv,f)\le c\,\rho(v,f).$$
--
--   This is the main result of §5: even when no single $H_\delta$ is a contraction, the optimality equation $v=Av$ has exactly one bounded solution, and it is the optimal return. Part (e) gives geometric convergence of successive approximations $A^{kN}v\to f$ from below.
--
--   **Formalization Note** The family $v$ is supplied with $H_\delta^Nv_\delta=v_\delta$ (the paper's definition of $v_\delta$ in §5; such a family exists and is unique because $H_\delta^N$ is a contraction on the complete space $V$); part (a) is a conclusion. $E$ is taken as an operator $V\to V$ with `IsNStageSupOperator H N E` (its value at each point is the least upper bound of $\{(H_\delta^Nv)(x)\}_\delta$); such an operator exists, which is the milestone Theorem 4 (a)–(c), and is then unique. $f$ is not defined as a fixed point: part (d) asserts that some $f\in V$ is the pointwise least upper bound of $\{v_\delta(x)\}_\delta$ (which determines $f$) and that this $f$ satisfies $Ef=f$, $Af=f$, is the only fixed point of either operator, and satisfies (e). $u\le v$ is pointwise, and $A^N$ is the $N$-fold composition.
-- source:
--   Denardo, Contraction Mappings in the Theory Underlying Dynamic Programming, SIAM Review 9(2) (1967), p. 169, Theorem 4 (proof pp. 169–170)

import Mathlib
import Definitions.Def_DenardoDP_NStage_Model

namespace DenardoDP.NStage

theorem theorem4 {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → DenardoDP.Contraction.BFun Ω → ℝ) (H : ((x : Ω) → D x) → DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω)
    (A : DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω) (v : ((x : Ω) → D x) → DenardoDP.Contraction.BFun Ω) (N : ℕ) (c : ℝ)
    (hH : DenardoDP.Contraction.IsPolicyOperator h H) (hA : DenardoDP.Contraction.IsMaxOperator h A)
    (hmono : DenardoDP.Contraction.MonotonicityAssumption H) (hN : NStageContractionAssumption H N c)
    (hv : ∀ δ, (H δ)^[N] (v δ) = v δ)
    (E : DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω) (hE : IsNStageSupOperator H N E) :
    (∀ δ, H δ (v δ) = v δ ∧ ∀ w, H δ w = w → w = v δ) ∧
    (∀ δ w, dist (v δ) w ≤ dist (H δ w) w * N / (1 - c)) ∧
    DenardoDP.Contraction.ModulusLE E c ∧
    ∃ f : DenardoDP.Contraction.BFun Ω, DenardoDP.Contraction.IsOptimalReturn v f ∧
      E f = f ∧ A f = f ∧ (∀ w, E w = w → w = f) ∧ (∀ w, A w = w → w = f) ∧
      (∀ w, DenardoDP.Contraction.PLe w f → dist (A^[N] w) f ≤ c * dist w f) := by sorry

end DenardoDP.NStage
