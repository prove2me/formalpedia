-- Prove2me | Theorems.Thm_BeyondConvexity_APTAS_theorem_1
-- name    : BeyondConvexity.APTAS.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:20:00.510108+00:00
-- url     : https://prove2.me/theorems/34ca3bb2-2191-4eb1-8b30-81d3f8664508
-- title:
--   Theorem 1 — full no-augmentation APTAS from rational-input representative rounding
-- statement:
--   Let P be a fixed class of the rational polygonal regions of Section 2, with holes and unrestricted finite boundary complexity. Assume uniform rasterizability and the effective rational-input restriction of representative roundability specified by RationalRoundability. Then P admits the full no-augmentation APTAS of Theorem 1.
--
--   There is one finite-alphabet machine, a computable exponent g(k), and a nonnegative integer additive allowance delta(k), chosen before the input instance. For every k >= 2 and every valid normalized class instance I, the machine returns a rational packing in exact unit-square bins, with disjoint interiors and boundary contact allowed, using at most (1+1/k) OPT(I)+delta(k) bins. OPT ranges over real translations. Runtime and the complete output encoding length are at most L^g(k), where L >= 2 is the binary polygon-input length.
--
--   For every real 0 < epsilon < 1, set k = ceil(1/epsilon)+1. The same machine at that index returns such an exact rational packing with at most (1+epsilon) OPT(I)+delta(k) bins, with the same effective polynomial runtime and output-length guarantees. All occurrences, including equal geometries, are packed. No rotation, bin enlargement, boundary-complexity bound, containment-width bound, computed optimal packing, or supplied good residue is assumed.
--
--   The rational-input hypothesis is weaker than the complete source assumption: a source procedure accepts every rational tuple and rational-scale partition in particular, and measuring time in the full supplied finite input cannot impose a stronger runtime bound. The source's geometric preprocessing produces only rational such queries of polynomial encoding length. The theorem thus specializes to the entire source claim for every class the source allows.
--
--   Differences from the source:
--   - generalization: uniform representative roundability for all admissible real parameters and real-scale partitions, with a uniform rational-parameter procedure → RationalRoundability, requiring the uniform procedure only for rational parameters and rational-scale partitions, with time polynomial in the full instance-plus-partition encoding; reason: restriction of the complete source procedure supplies this weaker hypothesis; every source instance is retained, and Section 3 and Appendix B.1 construct rational parameters and polynomial-length rational scales, so no part of the APTAS conclusion is restricted
--   - encoding: an APTAS for every real accuracy, with rational translations, computable parameter-dependent polynomial runtime and an instance-independent nonnegative integer additive constant → APTASScheme, specifying one finite-alphabet TM2 machine on integer accuracy indices, a computable exponent, exact rational output and its length, and the explicit bridge k = ceil(1/epsilon) + 1 for every real target accuracy; reason: the uniform rational-accuracy construction and Section 3 bridge supply the same complete real-accuracy guarantee; fixed binary encodings and operational execution bind all conclusions to the returned packing
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/890.pdf, Theorem 1, printed p.7 / PDF p.8; Definition 1, printed p.5 / PDF p.6; Definitions 3–5, printed pp.6–7 / PDF pp.7–8; Section 3 and Appendix B.1; Appendix D.9, printed pp.32–33 / PDF pp.33–34.

import Definitions.Def_BeyondConvexity_APTAS_RasterWitness
import Definitions.Def_BeyondConvexity_APTAS_RationalRoundability
import Definitions.Def_BeyondConvexity_APTAS_APTASScheme

namespace BeyondConvexity.APTAS

/-- Silva, Dell'Arriva, Miyazawa, STOC 2027 submission #890 (October 2026),
Theorem 1, printed p.7 / PDF p.8, with the full operational APTAS conclusion.
Generalization: only the rational-parameter, rational-scale restriction of
Definition 5 is required. Its complete source hypothesis supplies this restriction;
the rational preprocessing in Section 3 and Appendix B.1 uses only such queries.
All real target accuracies, exact unit bins, rational outputs, computable runtime
exponents, polynomial output length and instance-independent integer additive
constants are retained by APTASScheme. -/
theorem theorem_1 (P : Set Polygon)
    (hRaster : UniformlyRasterizable P)
    (hRound : RationalRoundability P) : APTASScheme P := by sorry

end BeyondConvexity.APTAS
