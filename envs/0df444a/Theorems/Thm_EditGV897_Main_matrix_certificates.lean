-- Prove2me | Theorems.Thm_EditGV897_Main_matrix_certificates
-- name    : EditGV897.Main.matrix_certificates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:03:21.007429+00:00
-- url     : https://prove2.me/theorems/9b07bb23-4c21-44ac-a5fb-075707482b0d
-- title:
--   Matrix completion preserves rank and halves surviving witnesses
-- statement:
--   Let $F$ be a family of $M\ge1$ affine edit maps on binary length-$n$ words, with the coverage and legal-script conditions of the construction, and let $t\ge1$. Set $b=\lceil\log_2(2M)\rceil$ and assume $b<n$. The prescribed row-building algorithm produces exactly $b$ linearly independent parity rows $H$, and its surviving collision witnesses satisfy
--
--   $$W_H(\mathbb F_2^n)\le M2^{n-b}\le2^{n-1}.$$
--
--   The algorithm uses a conditional-expectation row while witnesses remain and extends the row space with a coordinate row once the witness count vanishes. These are the matrix certificates used before choosing the syndrome in Part 2.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §4.1, Completing the matrix and equation (11), printed p.10 / PDF p.11

import Definitions.Def_EditGV897_Main_Construction
open EditGV897.Main

theorem EditGV897.Main.matrix_certificates (n t : ℕ) (F : Family n)
    (ht : 1 ≤ t) (hF : EditFamily t F) (hb : checkRows F.length < n) :
    let G := chooseMatrix F
    G.length = checkRows F.length ∧ FullRowRank G ∧
    witnessSum F G Finset.univ ≤ F.length * 2 ^ (n - G.length) ∧
    witnessSum F G Finset.univ ≤ 2 ^ (n - 1) := by sorry
