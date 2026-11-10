-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_lemma_A_1
-- name    : ChengCapClustering.Soft.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:51:58.116375+00:00
-- url     : https://prove2.me/theorems/61ecf00f-3351-4d3d-87e8-1fcb94fab96e
-- title:
--   Lemma A.1 — a $z$-certificate with $u+2^zv\le\beta^*_z+\eta$, computed in time depending only on $z$ and $\eta$
-- statement:
--   For fixed $z>1$ and $\eta\in(0,1]$, a $z$-certificate $(u,g,v)$ with $u+2^zv\le\beta^*_z+\eta$ can be computed in time that depends only on $z$ and $\eta$.
--
--   Differences from the source:
--   - encoding: an algorithm in the arithmetic model ("arithmetic operations and evaluations of dist(x, y)^z count as single steps") → an admissible program of `ChengCapClustering.Soft.Machine` (rational literals; parameters passed as real input) run on the stated input layout, halting within the stated number of steps with the stated output layout; reason: the source's cost model made operational; the output layout only names where the computed object is written
--   - reading: for fixed z > 1 and η, computed in time that depends only on z and η → one program reading z and η as real input, and a function T with at most T(z, η) steps for all z > 1, η ∈ (0, 1]; reason: with z and η hard-wired into the program the statement would only assert that such a certificate exists
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Lemma A.1, printed p. 46 / PDF p. 48

import Mathlib
import Definitions.Def_ChengCapClustering_Soft_Machine
import Definitions.Def_ChengCapClustering_Soft_Certificate

namespace ChengCapClustering.Soft

/-- Lemma A.1, printed p. 46 / PDF p. 48. One program, given `z > 1` and `η ∈ (0, 1]` as real input,
outputs a `z`-certificate `(u, g, v)` with `u + 2^z v ≤ β*_z + η` within a number of steps `T(z, η)`
that depends only on `z` and `η`. -/
theorem lemma_A_1 :
    ∃ prog : Program, Admissible prog ∧ ∃ T : ℝ → ℝ → ℝ,
      ∀ z η : ℝ, 1 < z → 0 < η → η ≤ 1 →
        HaltsWithin prog [] [z, η] (T z η)
          (fun s => ∃ u g v : ℝ, IsCertificate z u g v ∧
            u + (2 : ℝ) ^ z * v ≤ betaStar z + η ∧ OutputIs s [] [u, g, v]) := by sorry

end ChengCapClustering.Soft
