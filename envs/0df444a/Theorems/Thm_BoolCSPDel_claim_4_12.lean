-- Prove2me | Theorems.Thm_BoolCSPDel_claim_4_12
-- name    : BoolCSPDel.claim_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:28.365229+00:00
-- url     : https://prove2.me/theorems/3ef1c0d8-9e2c-4785-965d-143c4fdd1cdf
-- title:
--   Claim 4.12 — $f_B$ has bounded nonnegative integer frequencies and $\|f_B\|_1=O_k(n^k)$
-- statement:
--   Let $R\in\Gamma$ be nonempty and proper, $b\notin R$, $q$ select $b$ with $q(b)>0$, and $F_R=\max\{1,\max_x|q(x)|\}$. For any pinning instance $P$, the frequencies of $f_B(X,j)$ are nonnegative integers at most $F_R+1$, and at most $F_R$ if every scope of $P$ uses an additional variable. Moreover,
--
--   $$\|f_B\|_1\le|P|+F_R\,n^a,$$
--
--   with $a$ the arity of $R$. With $|P|=O_k(n+1)$ and $q$ fixed from $R$, this is $\|f_B\|_1=O_k(n^k)$.
--
--   These bounds make $f_B$ a legal instance with constant frequencies.
--
--   Differences from the source:
--   - encoding: ‖f_B‖₁ = O_k(n^k) → the explicit bound |P| + F_R n^a; reason: the O_k form follows at |P| = O_k(n + 1) with q fixed from R; the explicit form does not hide the dependence on q
--   - generalization: one relation R of arity k → a finite language Γ of relations of arity at most k; reason: the paper states this form on the cited page and uses it; Γ = {R} is the printed case
--   - generalization: no statement on individual frequencies in the claim → the frequency bounds of its proof, as conjuncts; reason: printed in the proof; p.27 says Theorem 4.2 relies on them
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Claim 4.12, (4.13), p.27; proof of Corollary 4.15, p.28

import Mathlib
import Definitions.Def_BoolCSPDel_fB

namespace BoolCSPDel

/-- **Claim 4.12 with the bounds of its proof.** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), Claim 4.12, (4.13), p.27, and the frequency
remark in the proof of Corollary 4.15, p.28.

The frequencies of `f_B` are nonnegative integers, at most `F_R` when every pinning scope uses a
variable of `Y` and at most `F_R + 1` in general, and `‖f_B‖₁ ≤ |P| + F_R nᵃ`, with `a` the arity.

**Formalization Note.** The page's `‖f_B‖₁ = O_k(n^k)` is this bound for `|P| = O_k(n + 1)` and `q` fixed
from `R`; the explicit form holds for every `P` and does not hide the dependence on `q`. -/
theorem claim_4_12 {k : ℕ} (Γ : Lang k) (R : Rel k) (hR : R ∈ Γ) (hR' : IsNonemptyProper R)
    (b : Fin R.1 → Bool) (hb : b ∉ R.2) (q : MvPolynomial (Fin R.1) ℤ) (hq : Selects R b q)
    (hqb : 0 < evalAt q b) {n Y : ℕ} (P : Finset (Con Γ ((Fin R.1 × Fin n) ⊕ Fin Y)))
    (X : (Fin R.1 → Fin n) → Bool) (j : Fin R.1 → Fin n) :
    (∀ C, 0 ≤ fB R hR P q b X j C ∧ fB R hR P q b X j C ≤ (freqBound q : ℤ) + 1) ∧
    ((∀ C ∈ P, ∃ i, (C.2 i).isRight) → ∀ C, fB R hR P q b X j C ≤ (freqBound q : ℤ)) ∧
    ∑ C, fB R hR P q b X j C ≤ (P.card : ℤ) + (freqBound q : ℤ) * (n : ℤ) ^ (R.1 : ℕ) := by sorry

end BoolCSPDel
