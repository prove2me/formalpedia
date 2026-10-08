-- Prove2me | Theorems.Thm_DenardoDP_NStage_theorem4_abc
-- name    : DenardoDP.NStage.theorem4_abc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:58:13.434146+00:00
-- url     : https://prove2.me/theorems/a93dde8c-5b9b-48ef-be20-38aabae98249
-- title:
--   Theorem 4 (a)–(c) — v_δ is the unique fixed point of H_δ, ρ(v_δ, v) ≤ ρ(H_δ v, v)N/(1 − c), and E exists and has modulus c
-- statement:
--   Work in Denardo's model under the **monotonicity** and **N-stage contraction** assumptions: there are a positive integer $N$ and $c<1$ such that every $H_\delta^N$ has modulus $c$ or less and every $H_\delta$ has modulus $1$ or less. For each policy $\delta$ let $v_\delta$ be the fixed point of the contraction $H_\delta^N$, $H_\delta^Nv_\delta=v_\delta$. Then:
--
--   1. (a) $v_\delta$ is the unique fixed point of $H_\delta$: $H_\delta v_\delta=v_\delta$, and $H_\delta w=w$ implies $w=v_\delta$;
--   2. (b) for every $\delta$ and every $v\in V$, $$\rho(v_\delta,v)\le\frac{\rho(H_\delta v,v)\,N}{1-c};$$
--   3. (c) the operator $E$, $(Ev)(x)=\sup_\delta(H_\delta^Nv)(x)$, maps $V$ into $V$ and has modulus $c$ or less;
--   4. the optimal return $f(x)=\sup_\delta v_\delta(x)$ is finite at every point and bounded, i.e. $f\in V$.
--
--   These are the statements the paper establishes in the text of §5 before stating Theorem 4 ("Parts (a)–(c) of the following theorem have just been established"). They are the first half of Theorem 4; the second half identifies $f$ as the unique fixed point of $E$ and of $A$.
--
--   **Formalization Note** The paper *defines* $v_\delta$ as the unique fixed point of $H_\delta^N$; here $v$ is a family of elements of $V$ with $H_\delta^Nv_\delta=v_\delta$ for each $\delta$ (which exists and is unique by the Banach fixed-point theorem), and $H_\delta v_\delta=v_\delta$ is a conclusion, not a hypothesis. Part (c) is stated existentially: there is an operator $E:V\to V$ whose value at each point is the least upper bound of $\{(H_\delta^Nv)(x)\}_\delta$, and it has modulus $c$ or less. The last clause asserts that $\{v_\delta(x)\}_\delta$ has a least upper bound at each point and that these form an element of $V$.
-- source:
--   Denardo, Contraction Mappings in the Theory Underlying Dynamic Programming, SIAM Review 9(2) (1967), p. 169, §5 text preceding Theorem 4, and Theorem 4 (a)–(c)

import Mathlib
import Definitions.Def_DenardoDP_NStage_Model

namespace DenardoDP.NStage

theorem theorem4_abc {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → DenardoDP.Contraction.BFun Ω → ℝ) (H : ((x : Ω) → D x) → DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω)
    (A : DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω) (v : ((x : Ω) → D x) → DenardoDP.Contraction.BFun Ω) (N : ℕ) (c : ℝ)
    (hH : DenardoDP.Contraction.IsPolicyOperator h H) (hA : DenardoDP.Contraction.IsMaxOperator h A)
    (hmono : DenardoDP.Contraction.MonotonicityAssumption H) (hN : NStageContractionAssumption H N c)
    (hv : ∀ δ, (H δ)^[N] (v δ) = v δ) :
    (∀ δ, H δ (v δ) = v δ ∧ ∀ w, H δ w = w → w = v δ) ∧
    (∀ δ w, dist (v δ) w ≤ dist (H δ w) w * N / (1 - c)) ∧
    (∃ E : DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω, IsNStageSupOperator H N E ∧ DenardoDP.Contraction.ModulusLE E c) ∧
    (∃ f : DenardoDP.Contraction.BFun Ω, DenardoDP.Contraction.IsOptimalReturn v f) := by sorry

end DenardoDP.NStage
