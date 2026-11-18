-- Prove2me | Theorems.Thm_EditGV897_Main_setup_certificates
-- name    : EditGV897.Main.setup_certificates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T01:57:29.7885+00:00
-- url     : https://prove2.me/theorems/14b73be5-dea1-4700-bc94-7c43c9915447
-- title:
--   Shared-parameter construction, witness bounds, and redundancy threshold
-- statement:
--   Fix $t\ge1$. The prescribed legal-script family and shared-parameter setup satisfy all combinatorial certificates beyond one threshold $N_t\ge1$. Writing $M=|F_{t,n}|$, $b=\lceil\log_2(2M)\rceil$, and $K=n-b-1$, the family covers every distinct confusable pair and
--
--   $$M\le(2t+1)[8(t+1)]^{2t}n^{2t}.$$
--
--   The computed matrix has exactly $b<n$ independent rows and the syndrome has length $b$. The total surviving witness count is at most both $M2^{n-b}$ and $2^{n-1}$. The selected coset satisfies
--
--   $$2^K\le |D_{H,\beta}|-W_H(D_{H,\beta}),\qquad b+1\le2t\log_2 n+C_t,$$
--
--   where the positive constant is $C_t=\log_2((2t+1)[8(t+1)]^{2t})+3$. These are the setup certificates used in the proof of Theorem 1. The displayed numerical constant is the mission's planning-derived admissible instantiation of the source's asymptotic bounds.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §3.1, §4.1–4.2, equations (11)–(12), and proof of Theorem 1, printed pp.7–13 / PDF pp.8–14

import Definitions.Def_EditGV897_Main_Codec
open EditGV897.Main

theorem EditGV897.Main.setup_certificates (t : ℕ) (ht : 1 ≤ t) :
    0 < redundancyConstant t ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        let F := canonicalFamily t n
        let P := setup t n
        EditFamily t F ∧ F.length ≤ familyCoefficient t * n ^ (2 * t) ∧
        P.rows.length = checkRows F.length ∧ P.rows.length < n ∧ FullRowRank P.rows ∧
        P.beta.length = P.rows.length ∧
        witnessSum F P.rows Finset.univ ≤ F.length * 2 ^ (n - P.rows.length) ∧
        witnessSum F P.rows Finset.univ ≤ 2 ^ (n - 1) ∧
        (2 ^ messageLength P : ℤ) ≤ signedBound F P.rows (coset P.rows P.beta) ∧
        (P.rows.length + 1 : ℕ) ≤ (2 * t : ℕ) * logTwo n + redundancyConstant t := by sorry
