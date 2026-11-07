-- Prove2me | Theorems.Thm_BoolCSPDel_lemma_3_10
-- name    : BoolCSPDel.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:52.289207+00:00
-- url     : https://prove2.me/theorems/2e4bffd1-3c10-40c2-bd32-89760ee74f6b
-- title:
--   Lemma 3.10 — $d_R(b)+s_R(b)=k$; a selection polynomial of degree $k-\deg_{\mathbb Z}(R)$
-- statement:
--   Let $R\subseteq\{0,1\}^k$ be nonempty and proper. For every unsatisfying tuple $b$,
--
--   $$d_R(b)+s_R(b)=k.$$
--
--   Consequently, with $d=\deg_{\mathbb Z}(R)$, some unsatisfying tuple $b$ has an integer multilinear selection polynomial $q$ of degree $k-d$ with $q(b)>0$.
--
--   This duality converts the capturing degree into the selection polynomial that drives the lower-bound reduction.
--
--   Differences from the source:
--   - encoding: q of degree k − d → degZ R + q.totalDegree = R.1; reason: avoids natural-number subtraction; same statement
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Lemma 3.10, p.21

import Mathlib
import Definitions.Def_BoolCSPDel_degZ

namespace BoolCSPDel

/-- **Lemma 3.10 (capturing and selection degrees).** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), Lemma 3.10, p.21; standing assumption of
§3.4, p.20: "every nonempty proper Boolean relation `R`, whether or not it is constant-satisfiable".

**Formalization Note.** `k` of the page is the arity `R.1`. "`q` of degree `k − d`" is written
`degZ R + q.totalDegree = R.1`, which avoids natural-number subtraction. -/
theorem lemma_3_10 {k : ℕ} (R : Rel k) (hR : IsNonemptyProper R) :
    (∀ b : Fin R.1 → Bool, b ∉ R.2 → dR R b + sR R b = R.1) ∧
    ∃ b : Fin R.1 → Bool, b ∉ R.2 ∧ ∃ q : MvPolynomial (Fin R.1) ℤ,
      IsMultilinear q ∧ Selects R b q ∧ degZ R + q.totalDegree = R.1 ∧ 0 < evalAt q b := by sorry

end BoolCSPDel
