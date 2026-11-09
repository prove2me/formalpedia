-- Prove2me | Theorems.Thm_EuclideanCRHardness_Covering_codec_roundtrips
-- name    : EuclideanCRHardness.Covering.codec_roundtrips
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:07.472857+00:00
-- url     : https://prove2.me/theorems/4e00b43a-ea63-4580-beb3-00cd470a67f2
-- title:
--   Binary codec round trips
-- statement:
--   Every integer field list, raw rational input, signed instance, unweighted parity instance, and weighted parity instance is recovered by parsing its canonical encoded bit string:
--   $$\operatorname{decode}(\operatorname{encode}(I))=I.$$
--   This supporting target makes representability explicit for all dimensions, empty lists, repeated occurrences, and arbitrary rational numerators and positive denominators.
--
--   Differences from the source:
--   - encoding: binary rational and combinatorial inputs → explicit signed binary fields, list parsers, and fixed failure on malformed strings; reason: fixes a conventional binary representation; runtime uses the inspected finite Turing-machine predicates
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), binary representation convention after Definition 1.1 and §3 input conventions, printed p. 1 / PDF p. 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf

import Definitions.Def_EuclideanCRHardness_Covering_Parity
import Definitions.Def_EuclideanCRHardness_Covering_RationalInput

namespace EuclideanCRHardness.Covering

/-- Fixed binary representations cover every raw object, including dimension zero.
These are codec correctness targets, not assumptions on hardness. -/
theorem codec_roundtrips :
    (∀ zs, wireDecode (wireEncode zs) = some zs) ∧
    (∀ I, decodeCR (encodeCR I) = some I) ∧
    (∀ G, decodeSigned (encodeSigned G) = some G) ∧
    (∀ P, decodeParity (encodeParity P) = some P) ∧
    (∀ P, decodeWeighted (encodeWeighted P) = some P) := by sorry

end EuclideanCRHardness.Covering
