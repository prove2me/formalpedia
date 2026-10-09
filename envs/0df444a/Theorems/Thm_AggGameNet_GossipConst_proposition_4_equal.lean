-- Prove2me | Theorems.Thm_AggGameNet_GossipConst_proposition_4_equal
-- name    : AggGameNet.GossipConst.proposition_4_equal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:55.001921+00:00
-- url     : https://prove2.me/theorems/73ae8271-9e65-453e-9ca0-affa98d288ed
-- title:
--   Proposition 4, equal probability and equal stepsize case
-- statement:
--   Let the aggregative game satisfy Assumptions 1, 3, 7 and 8, and suppose its map $\phi$ is strongly monotone with modulus $\mu>0$. Run the gossip scheme with constant positive steps $\alpha_i=\alpha$ and equal update probabilities $p_i=p$, where $0<\alpha<1/(2\mu p)$. Let $C$ bound the gradient evaluations as in Lemma 3, let $\lambda\in(0,1)$ satisfy (30), choose $M$ bounding the diameter of every $K_i$, and set $B=(\max_i\bar L_i)NM$. There is a unique solution $x^*$ of $\operatorname{VI}(K,\phi)$ and
--
--   $$\limsup_{k\to\infty}\mathbb E\|x^k-x^*\|^2\le\frac\alpha\mu\left(2C^2N+\frac{BC\sqrt{2nN}}{1-\sqrt\lambda}\right).$$
--
--   This is the paper's final special case on p. 29, giving a persistent mean-square error bound for constant-step gossip. **Formalization Note** Assumption 3 holds for all aggregate arguments so the algorithm is defined at $N\hat v_i^k$; the initial profile is deterministic, and expectations are nonnegative extended-real integrals. The printed general Proposition 4 has gaps in (53) and (54), which vanish when both steps and update probabilities are equal. Assumption 8 remains a standing hypothesis of Proposition 4 although it is unused in this special case.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, Proposition 4 special case, final display, p. 29

import Mathlib
import Definitions.Def_AggGameNet_GossipConst_Gossip

open MeasureTheory ProbabilityTheory Filter

namespace AggGameNet.GossipConst

theorem proposition_4_equal {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (AggGameNet.Sync.E n)) (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n)
    (h1 : AggGameNet.Sync.Assumption1 K F) (Lbar : Fin N → ℝ)
    (h3 : AggGameNet.Sync.Assumption3 K F Lbar)
    (G : SimpleGraph (Fin N)) (h7 : G.Connected)
    (p : Fin N → Fin N → ℝ) (hp : AggGameNet.Gossip.GossipProbs G p)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (I J : ℕ → Ω → Fin N)
    (hdraw : AggGameNet.Gossip.GossipDraws P I J p)
    (L : Fin N → ℝ) (h8 : Assumption8 K F L)
    (mu : ℝ) (hmu : 0 < mu) (hsm : StronglyMonotone K F mu)
    (alpha : Fin N → ℝ) (halpha : ∀ i, 0 < alpha i)
    (x v : ℕ → Ω → Fin N → AggGameNet.Sync.E n)
    (hrun : IsGossipRun K F I J alpha x v)
    (pp : ℝ) (hpeq : ∀ i, AggGameNet.Gossip.pbar p i = pp)
    (a : ℝ) (haeq : ∀ i, alpha i = a) (ha : a < 1 / (2 * mu * pp))
    (C : ℝ) (hCrun : ∀ ω i k,
      ‖F i (x k ω i) ((N : ℝ) • AggGameNet.Gossip.vhat I J v k ω i)‖ ≤ C)
    (hCK : ∀ i, ∀ xi ∈ K i, ∀ u ∈ AggGameNet.Sync.Kbar K, ‖F i xi u‖ ≤ C)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (h30 : Contraction30 P I J lam)
    (M : ℝ) (hM : ∀ i, ∀ xi ∈ K i, ∀ zi ∈ K i, ‖xi - zi‖ ≤ M) :
    ∃ xs, AggGameNet.Gossip.IsVISol K F xs ∧ (∀ y, AggGameNet.Gossip.IsVISol K F y → y = xs) ∧
      Filter.limsup
        (fun k => ∫⁻ ω, ENNReal.ofReal (∑ i, ‖x k ω i - xs i‖ ^ 2) ∂P)
        atTop ≤
        ENNReal.ofReal
          ((a / mu) *
            (2 * C ^ 2 * (N : ℝ) +
              (sSup (Set.range Lbar) * (N : ℝ) * M) * C *
                Real.sqrt (2 * (n : ℝ) * (N : ℝ)) / (1 - Real.sqrt lam))) := by sorry

end AggGameNet.GossipConst
