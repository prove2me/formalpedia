-- Prove2me | Theorems.Thm_AMRangeAvoid_Characterization_Supplement_theorem_1_11
-- name    : AMRangeAvoid.Characterization.Supplement.theorem_1_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:30:58.106697+00:00
-- url     : https://prove2.me/theorems/dfe6f86a-0bef-4124-92ed-3fc40847963c
-- title:
--   Theorem 1.11 — Both natural Avoid-family consequences for graphs and lattices
-- statement:
--   There exist deterministic polynomial-time graph- and lattice-to-SSLB reduction programs and an SSLB targeted-hitting reduction $(f,g)$ for the published verifier. Their literal compositions define the two expanding-circuit families $f_{\mathrm{GNI}}$ and $f_{\mathrm{SVP}}$. With the same factor $\gamma(n)=400\lceil\sqrt{n/\log_2 n}\rceil$ for $n\ge2$ and $\gamma(1)=400$, their independent consequences are
--
--   $$\mathrm{Avoid}_{f_{\mathrm{GNI}}}\in\mathrm{SearchNP}\ \Longrightarrow\ \mathrm{GNI},\mathrm{GI}\in\mathrm{NP}\cap\mathrm{coNP},$$
--   $$\mathrm{Avoid}_{f_{\mathrm{SVP}}}\in\mathrm{SearchNP}\ \Longrightarrow\ \overline{\mathrm{GapSVP}}_\gamma\in\mathrm{prNP}\ \land\ \mathrm{GapSVP}_\gamma\in\mathrm{prNP}\cap\mathrm{prcoNP}.$$
--
--   This one item states the joint formal content of Corollaries 5.2 and 5.3, as referenced by introductory Theorem 1.11. Each implication requires only its own family-specific algorithm. The graph conclusions concern complementary total languages; the lattice conclusions concern promise classes.
--
--   Differences from the source:
--   - encoding: the two composed families named in Corollaries 5.2 and 5.3 → existentially produced operational reduction maps and their literal compositions with a single SSLB Avoid producer; reason: existence and correctness of the programs are conclusions, and both family-specific implications are retained independently
--   - encoding: graph inputs and the factor formula with log₂ n → the same decidable total graph-code extension and gamma(1)=400 used in Theorems 4.4 and 4.6; reason: the complementary graph languages agree on every graph pair, and exact dimension-one lattice inputs are retained
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), Theorem 1.11, printed p.5 (PDF p.7); formal content Corollaries 5.2–5.3, printed p.25 (PDF p.27); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Supplement_Families
import Definitions.Def_AMRangeAvoid_Characterization_SSLB

namespace AMRangeAvoid.Characterization.Supplement

theorem theorem_1_11 :
    ∃ graphMap latticeMap : Bits → Bits,
      DecisionMap GNI SSLB graphMap ∧
      DecisionMap (CoGapSVP gamma) SSLB latticeMap ∧
      ∃ f : Bits → Bits, ∃ g : Bits → Bits → Bits,
        IsAvoidReduction (TargetedHitting SSLB sslbVerifier) f g ∧
        (InSearchNP (AvoidFamily (composedFamily graphMap f)) →
          InPrNPCoNP GNI ∧ InPrNPCoNP GI) ∧
        (InSearchNP (AvoidFamily (composedFamily latticeMap f)) →
          InPrNP (CoGapSVP gamma) ∧ InPrNPCoNP (GapSVP gamma)) := by sorry

end AMRangeAvoid.Characterization.Supplement
