-- Prove2me | Theorems.Thm_ChoresTIE197_Main_Supplement_lemma_5_4
-- name    : ChoresTIE197.Main.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:00:50.995199+00:00
-- url     : https://prove2.me/theorems/6aa0c788-1e3c-4a7b-9453-d767fe93b177
-- title:
--   Lemma 5.4 — ordinary-cost bound at a single exaggerated report
-- statement:
--   Fix $n\ge4$, $1\le\alpha<13/12$ and $\varepsilon>0$ with $\alpha(11+\varepsilon)<12$. Use exactly the two Table 5 rows on $n+7$ chores, and let $F$ be any complete payment-free randomized mechanism with the ex-post $\alpha$-MMS guarantee at every positive report profile. For any named agent $i$, form the profile $c^{(i)}$ where she reports $c_1$ and every other agent reports $c_0$. For every complete allocation $A$ with nonzero probability under $F(c^{(i)})$,
--   $$
--   c_0(A_i)\le11.
--   $$
--   The cost in this conclusion is the ordinary row $c_0$, even though the recipient reports $c_1$. The statement is support-wise, not merely an expectation bound. The condition on $\varepsilon$ implies $\varepsilon<1$; singleton costs may be zero in the general domain, while these two particular rows have positive singleton costs. Their actual MMS values are computed by the published definition, rather than supplied as assumptions.
--
--   This supports Theorem 5.3. The combinatorial restriction needs no truthfulness assumption, which is explicitly recorded as a generalization below.
--
--   Differences from the source:
--   - encoding: finite agents and chores, arbitrary nonnegative additive costs, complete payment-free randomized allocations → Fin-indexed nonnegative real singleton tables and the published PMF on complete owner maps, with cost MMS the sign dual of utility MMS; reason: finite relabeling and sign duality preserve every source instance, empty bundles, real probabilities and support-wise guarantees
--   - encoding: the standing convention on p.7 assumes positive MMS for every agent → MMSOn Positive α F on all profiles with positive row total; reason: for nonnegative additive costs and n≥2, positive total is equivalent to positive MMS; no singleton positivity is required, and full-domain guarantees restrict to this domain
--   - encoding: eleven named core chores and n−4 huge chores with the Table 5 rows → Fin (n+7), with the first eleven zero-based indices in Table 5 order and a nonnegative real subtype for ε; reason: when n≥4 the indexing gives exactly the source chores and every positive real ε is represented; n=4 gives no huge chores
--   - encoding: §5.3 fixes n≥4, an approximation ratio below 13/12 and sufficiently small ε>0 → 4≤n, 1≤α, α<13/12, 0<ε and α(11+ε)<12; reason: the lower bound α≥1 is Definition 2.3’s approximation convention; the explicit smallness condition is the source choice and already implies ε<1, so no redundant ε<1 hypothesis is added
--   - generalization: Lemma 5.4 occurs within the assumed complete TIE mechanism of §5.3 → only completeness and the assumed ex-post α-MMS guarantee on Positive are premises; TIE is omitted; reason: the support restriction in the proof uses only the MMS caps and packing the remaining chores; adding TIE specializes back to every source mechanism
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Lemma 5.4, printed p.28, PDF p.28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Setting
import Definitions.Def_ChoresTIE197_Main_Supplement_Table5

open scoped NNReal ENNReal

open Finset

namespace ChoresTIE197.Main.Supplement

/-- Lemma 5.4, printed/PDF pp.28–29, with the hypotheses inherited from §5.3.
No TIE premise is needed for this support restriction. MMS values and the
ordinary-cost bound are conclusions of the source argument, not input data. -/
theorem lemma_5_4 (n : ℕ) (hn : 4 ≤ n) (α : ℝ)
    (hα_lower : 1 ≤ α) (hα_upper : α < 13 / 12)
    (ε : ℝ≥0) (hε : 0 < ε) (hsmall : α * (11 + (ε : ℝ)) < 12)
    (F : Mechanism n (n + 7)) (hMMS : MMSOn Positive α F)
    (i : Fin n) (A : Allocation n (n + 7))
    (hsupport : F (singleReport n ε i) A ≠ 0) :
    cost (ordinary n ε) (bundle A i) ≤ 11 := by sorry

end ChoresTIE197.Main.Supplement
