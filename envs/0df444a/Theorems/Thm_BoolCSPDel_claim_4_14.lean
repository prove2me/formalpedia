-- Prove2me | Theorems.Thm_BoolCSPDel_claim_4_14
-- name    : BoolCSPDel.claim_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:38.394202+00:00
-- url     : https://prove2.me/theorems/4e8b3af5-2c74-4741-ac1d-2526ea3689d3
-- title:
--   Claim 4.14 — $f_B(X,j)$ is unsatisfiable if and only if $X_j=1$
-- statement:
--   Let $R\in\Gamma$ be nonempty and proper, $b\notin R$, $q$ select $b$ with $q(b)>0$, and let $P$ pin $\alpha_j$ up to $\mathrm{Aut}(\Gamma)$. For every $X$ and $j$, the instance $f_B(X,j)$ is unsatisfiable if and only if $X_j=1$.
--
--   This is the correctness of the reduction from INDEX.
--
--   Differences from the source:
--   - generalization: one relation R of arity k → a finite language Γ of relations of arity at most k; reason: the paper states this form on the cited page and uses it; Γ = {R} is the printed case
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Claim 4.14, p.27; proof of Corollary 4.15, p.28

import Mathlib
import Definitions.Def_BoolCSPDel_fB

namespace BoolCSPDel

/-- **Claim 4.14 in language form.** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), Claim 4.14, p.27, with the change of Corollary 4.15, p.28
("Bob can enforce `α_j` up to one common automorphism of `Γ`").

For a relation `R ∈ Γ`, `q` selecting `b` with `q(b) > 0`, and `P` pinning `α_j` up to `Aut(Γ)`, the instance
`f_B(X, j)` is unsatisfiable if and only if `X_j = 1`. `Γ = {R}` is the printed form. -/
theorem claim_4_14 {k : ℕ} (Γ : Lang k) (R : Rel k) (hR : R ∈ Γ) (hR' : IsNonemptyProper R)
    (b : Fin R.1 → Bool) (hb : b ∉ R.2) (q : MvPolynomial (Fin R.1) ℤ) (hq : Selects R b q)
    (hqb : 0 < evalAt q b) {n Y : ℕ} (X : (Fin R.1 → Fin n) → Bool) (j : Fin R.1 → Fin n)
    (P : Finset (Con Γ ((Fin R.1 × Fin n) ⊕ Fin Y))) (hP : IsPinning P (alphaJ b j)) :
    ¬ (Sat (fB R hR P q b X j)).Nonempty ↔ X j = true := by sorry

end BoolCSPDel
