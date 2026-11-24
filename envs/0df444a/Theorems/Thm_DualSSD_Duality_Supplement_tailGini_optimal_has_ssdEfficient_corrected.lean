-- Prove2me | Theorems.Thm_DualSSD_Duality_Supplement_tailGini_optimal_has_ssdEfficient_corrected
-- name    : DualSSD.Duality.Supplement.tailGini_optimal_has_ssdEfficient_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:41:49.265854+00:00
-- url     : https://prove2.me/theorems/e5dc3607-5351-4a46-9c33-cf32968d8a30
-- title:
--   Theorem 5.5 (corrected: endpoint preservation and nonempty Q) — tail-Gini optimal efficiency
-- statement:
--   Let $(\Omega,\mathcal B,P)$ be any probability space and $1<q<\infty$. Let $Q$ be a nonempty, convex, norm-bounded, norm-closed subset of $L_q(\Omega,P)$. For $0<p<1$ and $0<\lambda\le1$, write $\mu_X=E_P X$, let $G_X(p)$ be the tail Gini measure (4.8), and define the actual optimizer set
--   $$Q^* = \{X\in Q:\ \mu_Z-\lambda G_Z(p)\le\mu_X-\lambda G_X(p)\ \text{for every } Z\in Q\}.$$
--   Then
--   $$Q^*\ne\varnothing,\qquad
--   \forall X\in Q^*\ \exists X^*\in Q^*:\ X^*\text{ is SSD-efficient in }Q,
--   \quad \mu_{X^*}\ge\mu_X,\quad G_{X^*}(p)\ge G_X(p),\quad \lambda<1\Longrightarrow
--   \bigl(\mu_{X^*}=\mu_X\ \text{and}\ G_{X^*}(p)=G_X(p)\bigr).$$
--   SSD-efficiency is measured in the original feasible set $Q$, not merely among optimizers. This is a corrected companion to the inherited dominance characterization, with Proposition 4.6 providing its new supporting result. The equalities remain jointly attached to the same efficient replacement of each optimizer.
--
--   **Formalization Note** The printed Theorem 5.5 is false at $\lambda=1$ even for a compact convex nonempty set in $L_2$; DISPROOF.md retains the exact counterexample and the source proof gap. This statement still covers $\lambda=1$, with existence, efficient replacement and the inequalities $\mu_{X^*}\ge\mu_X$, $G_{X^*}(p)\ge G_X(p)$ (the halves of the printed equalities that the counterexample does not refute), and asserts both preservation equalities for $\lambda<1$. Nonemptiness of $Q$ is an explicit repair of a separate empty-set defect. The exponent is finite and real, not restricted to integers. Integrability follows from $L_q\subseteq L_1$ on a probability space. The optimizer predicate is expanded directly from (5.1); its value is never assumed in a hypothesis.
--
--   Differences from the source:
--   - correction: Q is convex, bounded and closed, without explicit nonemptiness → Q.Nonempty is required as well; reason: Q=∅ satisfies the printed hypotheses and has no optimizer; this repairs existence and excludes exactly empty feasible sets
--   - correction: mean and tail-Gini preservation are asserted for every 0<λ≤1 → the full parameter range 0<λ≤1 retains existence, efficient replacement and μ_{X*}≥μ_X, G_{X*}(p)≥G_X(p), while the two preservation equalities are guaranteed only if λ<1; reason: the nonempty two-atom L2 segment in DISPROOF.md refutes the ≤ halves of both equalities at λ=1 (the mean weight 1−λ in the source argument vanishes there); the ≥ halves survive and are kept
--   - encoding: the usual Lq space for a finite real exponent q>1 → MeasureTheory.Lp ℝ q P with 1<q and q≠⊤, evaluated via its a.e. representative; reason: ENNReal permits ∞ syntactically, so q≠⊤ expresses the finite exponent of the reflexive Lq setting; no finite-dimensional restriction is made
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13(1):60–78 (2002), DOI 10.1137/S1052623400375075, p. 74 (PDF page 15), Theorem 5.5; corrected using the preceding Theorem 5.4 proof and eqs. (4.8), (5.1); see DISPROOF.md

import Mathlib
import Definitions.Def_DualSSD_MeanRisk_gini
import Definitions.Def_DualSSD_MeanRisk_ssdEfficient

namespace DualSSD.Duality.Supplement

open MeasureTheory

/-- Theorem 5.5 (corrected), p. 74. Nonemptiness of Q is explicit. For every lam in (0,1]
the efficient replacement has mean and tail Gini at least those of X; the printed equalities
are asserted for lam<1 only, since at lam=1 their `≤` halves are false. See the supplement's
DISPROOF.md. -/
theorem tailGini_optimal_has_ssdEfficient_corrected
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ENNReal) [Fact (1 ≤ q)] (hq : 1 < q) (hqtop : q ≠ ⊤)
    (Q : Set (Lp ℝ q P)) (hQconv : Convex ℝ Q) (hQbdd : Bornology.IsBounded Q)
    (hQclosed : IsClosed Q) (hQne : Q.Nonempty)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    (∃ X ∈ Q, ∀ Z ∈ Q,
      DualSSD.MeanRisk.mean P ⇑Z - lam * DualSSD.MeanRisk.tailGini P ⇑Z p ≤
        DualSSD.MeanRisk.mean P ⇑X - lam * DualSSD.MeanRisk.tailGini P ⇑X p) ∧
    ∀ X ∈ Q,
      (∀ Z ∈ Q,
        DualSSD.MeanRisk.mean P ⇑Z - lam * DualSSD.MeanRisk.tailGini P ⇑Z p ≤
          DualSSD.MeanRisk.mean P ⇑X - lam * DualSSD.MeanRisk.tailGini P ⇑X p) →
      ∃ Xstar ∈ Q,
        (∀ Z ∈ Q,
          DualSSD.MeanRisk.mean P ⇑Z - lam * DualSSD.MeanRisk.tailGini P ⇑Z p ≤
            DualSSD.MeanRisk.mean P ⇑Xstar - lam * DualSSD.MeanRisk.tailGini P ⇑Xstar p) ∧
        DualSSD.MeanRisk.SSDEfficient P
          ((fun Z : Lp ℝ q P => (⇑Z : Ω → ℝ)) '' Q) ⇑Xstar ∧
        DualSSD.MeanRisk.mean P ⇑X ≤ DualSSD.MeanRisk.mean P ⇑Xstar ∧
        DualSSD.MeanRisk.tailGini P ⇑X p ≤ DualSSD.MeanRisk.tailGini P ⇑Xstar p ∧
        (lam < 1 →
          DualSSD.MeanRisk.mean P ⇑Xstar = DualSSD.MeanRisk.mean P ⇑X ∧
          DualSSD.MeanRisk.tailGini P ⇑Xstar p = DualSSD.MeanRisk.tailGini P ⇑X p) := by sorry

end DualSSD.Duality.Supplement
