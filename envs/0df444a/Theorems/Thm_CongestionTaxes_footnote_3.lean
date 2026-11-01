-- Prove2me | Theorems.Thm_CongestionTaxes_footnote_3
-- name    : CongestionTaxes.footnote_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:36:28.244594+00:00
-- url     : https://prove2.me/theorems/834ff5e9-81e2-4064-a3d6-522ca8d92262
-- title:
--   Footnote 3, p.4 — equilibrium classes are nested and pure equilibria exist under taxes
-- statement:
--   Let $G$ be a congestion game whose agents have nonempty strategy sets, and let $(v_r)_r$ be any real parameter vector. In the game with perceived costs $\bar C_i(a)=\sum_{r\in a_i}f_r(|a|_r,v_r)$:
--
--   1. a pure Nash equilibrium exists;
--   2. every pure Nash equilibrium, played as point-mass lotteries, is a mixed Nash equilibrium;
--   3. the product distribution of every mixed Nash equilibrium is a correlated equilibrium;
--   4. every correlated equilibrium is a coarse correlated equilibrium;
--   5. consequently the sets of (expected) social costs of pure, mixed, correlated and coarse correlated equilibria are nested in this order;
--   6. for every class the set of equilibrium social costs is nonempty.
--
--   So the price of anarchy (3) is well defined for every class.
--
--   Differences from the source:
--
--   - generalization: congestion games where taxes are used → any real parameter vector $v$ (taxes of any sign); reason: the potential argument does not use the sign; the paper's taxes are the case $v\ge0$
--   - encoding: each class is a superset of the previous → explicit identifications (pure profile ↦ point-mass lotteries ↦ product distribution) and inclusion of the equilibrium social costs; reason: the classes live on different types; the identifications are the standard ones
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, footnote 3, p.4

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_CongestionPoA_Mixed_Model
import Definitions.Def_RobustPoA_Static_Distribution
import Definitions.Def_CongestionTaxes_taxedGame
import Definitions.Def_CongestionTaxes_perceivedCost
import Definitions.Def_CongestionTaxes_IsCorrelatedEq
import Definitions.Def_CongestionTaxes_EqClass
import Definitions.Def_CongestionTaxes_equilibriumCosts

namespace CongestionTaxes

/-- Footnote 3 (Paccagnan, Gairing, arXiv:2105.07480v2, p.4): each class of equilibria is a
superset of the previous one, pure Nash equilibria exist in congestion games with taxes, and so
all equilibrium sets are nonempty. For every congestion game `G` whose agents have nonempty
strategy sets and every parameter vector `v` (any real taxes), in the taxed game:
1. a pure Nash equilibrium exists;
2. a pure Nash equilibrium `a`, played as point-mass lotteries, is a mixed Nash equilibrium;
3. the product distribution of a mixed Nash equilibrium is a correlated equilibrium;
4. every correlated equilibrium is a coarse correlated equilibrium;
5. the social costs of pure ⊆ mixed ⊆ correlated ⊆ coarse correlated equilibria;
6. for every class the set of equilibrium social costs is nonempty.

**Formalization Note** Mixed profiles are the published `CongestionPoA.Mixed` lotteries on each
`G.strategies i`, and their product is `AGT.profileProb`, made a finitely supported distribution
by `Finsupp.equivFunOnFinite`. The statement holds for every real parameter vector, as the
footnote claims ("even in congestion games where taxes are used"). -/
theorem footnote_3 {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (hne : ∀ i, (G.strategies i).Nonempty)
    (v : E → ℝ) :
    (∃ a, CongestionPoA.AsymSum.IsPureNash (taxedGame G v) a) ∧
    (∀ a, CongestionPoA.AsymSum.IsPureNash (taxedGame G v) a →
      CongestionPoA.Mixed.IsMixedNash (taxedGame G v)
        (fun i (t : ↥(G.strategies i)) => if (t : Finset E) = a i then (1 : ℝ) else 0)) ∧
    (∀ σ : (∀ i, ↥(G.strategies i) → ℝ), CongestionPoA.Mixed.IsMixedNash (taxedGame G v) σ →
      IsCorrelatedEq (perceivedCost G v) (Finsupp.equivFunOnFinite.symm (AGT.profileProb σ))) ∧
    (∀ σ, IsCorrelatedEq (perceivedCost G v) σ →
      RobustPoA.Static.IsCCE (perceivedCost G v) σ) ∧
    (equilibriumCosts .pure G v ⊆ equilibriumCosts .mixed G v ∧
      equilibriumCosts .mixed G v ⊆ equilibriumCosts .correlated G v ∧
      equilibriumCosts .correlated G v ⊆ equilibriumCosts .coarseCorrelated G v) ∧
    ∀ K : EqClass, (equilibriumCosts K G v).Nonempty := by sorry

end CongestionTaxes
