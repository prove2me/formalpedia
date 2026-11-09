-- Prove2me | Theorems.Thm_ChoresTIE197_Main_lemma_3_2
-- name    : ChoresTIE197.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:20:30.604229+00:00
-- url     : https://prove2.me/theorems/2b9641b3-1b9f-4d9e-afbd-95b2dac0a625
-- title:
--   Lemma 3.2 — right-saturating multigraph decomposition
-- statement:
--   Let $G=(L\cup R,E)$ be a finite bipartite multigraph and $d\ge1$ an integer. Suppose every left vertex has degree at most $d$ and every right vertex has degree exactly $d$. Then
--   $$E=E_1\sqcup\cdots\sqcup E_d,$$
--   where every $E_a$ is a matching saturating every vertex of $R$. Edge identities distinguish parallel edges. Empty vertex or edge sets are allowed when the degree hypotheses hold. This is the combinatorial existence result used by the nomination decomposition.
--
--   Differences from the source:
--   - encoding: finite bipartite multigraph G with d matchings decomposing E → finite edge identities, endpoint maps and a total coloring E to Fin d; reason: color fibers partition every edge exactly once, parallel edges remain distinct, and each fiber is a right-saturating matching
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Lemma 3.2, printed p.9, PDF p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Families

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

theorem lemma_3_2 {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq E] (left : E → L) (right : E → R) (d : ℕ) (hd : 1 ≤ d)
    (hleft : ∀ v, (univ.filter (fun e => left e = v)).card ≤ d)
    (hright : ∀ v, (univ.filter (fun e => right e = v)).card = d) :
    ∃ color : E → Fin d,
      ∀ a : Fin d,
        ProphetBipartite.IsMatching left right (univ.filter (fun e => color e = a)) ∧
        ∀ v : R, ∃ e, color e = a ∧ right e = v := by sorry

end ChoresTIE197.Main
