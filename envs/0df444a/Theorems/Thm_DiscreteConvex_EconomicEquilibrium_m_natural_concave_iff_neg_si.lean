-- Prove2me | Theorems.Thm_DiscreteConvex_EconomicEquilibrium_m_natural_concave_iff_neg_si
-- name    : DiscreteConvex.EconomicEquilibrium.m_natural_concave_iff_neg_si
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T05:08:35.665094+00:00
-- url     : https://prove2.me/theorems/deff9a30-3999-464d-b864-9b388e9477f9
-- title:
--   Theorem 11.4 -- M$^\natural$-concavity via the single improvement axiom
-- statement:
--   **Theorem 11.4** (p.330). For a function $U : \mathbb Z^K \to \mathbb R \cup \{-\infty\}$ with a nonempty effective domain, $U$ is an M$^\natural$-concave function if and only if $U$ satisfies ($-$M$^\natural$-SI[Z]).
--
--   This is the concave-utility analogue of chunk 06's M$^\natural$-exchange-axiom characterization (Theorem 6.2): the abstract exchange-axiom definition of M$^\natural$-concavity is shown equivalent to a single-step "ascent" property, which is the form used to connect M$^\natural$-concavity to the gross-substitutes and no-complementarities properties from mathematical economics (Theorem 11.7 and the surrounding discussion).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.330, Theorem 11.4.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.330, Theorem 11.4

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_NegSI
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_UDom

namespace DiscreteConvex.EconomicEquilibrium

/-- Theorem 11.4 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.330). For a function
`U : Zᴷ → R ∪ {−∞}` with a nonempty effective domain, `U` is an M♮-concave function if and only if
`U` satisfies (−M♮-SI[Z]). -/
theorem m_natural_concave_iff_neg_si {K : Type*} [Fintype K] [DecidableEq K]
    (U : (K → ℤ) → WithBot ℝ) (hU : (UDom U).Nonempty) :
    MNaturalConcave U ↔ NegSI U := by sorry

end DiscreteConvex.EconomicEquilibrium
