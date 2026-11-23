-- Prove2me | Theorems.Thm_ConformalRiskControl_risk_lower_bound
-- name    : ConformalRiskControl.risk_lower_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:13:46.744389+00:00
-- url     : https://prove2.me/theorems/641962f0-2056-4c1e-8702-a2e3ae8f1304
-- title:
--   Theorem 2 (as proved): the risk is at least $\alpha - 2B/(n+1)$
-- statement:
--   Let $a<b$, $\Lambda=[a,b]$, $n\ge1$ and $\alpha<B$. Let $L_1,\dots,L_{n+1}:\Lambda\to\mathbb{R}$ be i.i.d. random functions with non-increasing, right-continuous realisations. Assume that almost surely, for every $i$:
--
--   1. $L_i(b)\le\alpha$ and $0\le L_i(\lambda)\le B$ for all $\lambda\in\Lambda$;
--   2. $L_i(a)\ge\alpha$.
--
--   Assume also that $\mathbb{P}(J(L_i,\lambda)>0)=0$ for every $i$ and every $\lambda\in(a,b]$. Then the conformal risk control parameter $\hat\lambda$ of eq. (4) satisfies
--   $$\mathbb{E}\big[L_{n+1}(\hat\lambda)\big]\ge\alpha-\frac{2B}{n+1}.$$
--
--   So the procedure is not conservative by more than $2B/(n+1)$.
--
--   **Formalization Note** Hypothesis 2 is not in the paper. Without it the printed theorem is false: if $L_i\equiv0$ on $[0,1]$, $B=1$, $\alpha=1/2$ and $n\ge4$, then $\hat\lambda=0$ and $\mathbb{E}[L_{n+1}(\hat\lambda)]=0<\alpha-2/(n+1)$. The proof needs the infimum $\hat\lambda''$ to have a left neighbourhood on which the criterion fails. Hypothesis 2 guarantees this, and it holds in the paper's examples, where the smallest parameter gives the largest loss. The jump is defined through a left limit, so $\Lambda$ is the interval $[a,b]$.
-- source:
--   Angelopoulos, Bates, Fisch, Lei and Schuster, Conformal Risk Control, arXiv:2208.02814v4, Section 2.2, Theorem 2, p. 4; proof in Appendix B, p. 16

import Mathlib
import Definitions.Def_ConformalRiskControl_Basic

open MeasureTheory ProbabilityTheory Filter

namespace ConformalRiskControl

theorem risk_lower_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (a b : ℝ) (hab : a < b) (B α : ℝ)
    (hαB : α < B) (L : Fin (n + 1) → Ω → ℝ → ℝ) (hiid : IsIID P (Set.Icc a b) L)
    (hanti : ∀ i ω, AntitoneOn (L i ω) (Set.Icc a b))
    (hrc : ∀ i ω, IsRightContOn (Set.Icc a b) (L i ω))
    (h5 : ∀ᵐ ω ∂P, ∀ i, LossBounds (Set.Icc a b) B α (L i ω))
    (hnonneg : ∀ᵐ ω ∂P, ∀ i, ∀ x ∈ Set.Icc a b, 0 ≤ L i ω x)
    (hjump : ∀ i, ∀ x ∈ Set.Ioc a b, P {ω | 0 < jump (L i ω) x} = 0)
    (hend : ∀ᵐ ω ∂P, ∀ i, α ≤ L i ω a) :
    ((α - 2 * B / (n + 1) : ℝ) : EReal) ≤
      upperExp P B (fun ω =>
        L (Fin.last n) ω (lhat (Set.Icc a b) B α (fun i : Fin n => L i.castSucc ω))) := by sorry

end ConformalRiskControl
