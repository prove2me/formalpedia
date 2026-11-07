-- Prove2me | Theorems.Thm_AvgValueAlloc_lemma_3_1
-- name    : AvgValueAlloc.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:01.503318+00:00
-- url     : https://prove2.me/theorems/d7b4868c-5470-4e0c-91ad-b78e4a9f32d9
-- title:
--   Lemma 3.1 — Independent adaptive-bank validation (9)
-- statement:
--   Let $\rho\in\mathbb Q^n_{>0}$, $D$ a finite law, $M$ fixed funding items whose ambiguity is at most $\sigma$, and $q\ge1$ independent cohorts $Y_1,\dots,Y_q$ of $r$ records drawn from $D$. Put $\hat g(B)=q^{-1}\sum_bG_{Y_b}(B)$ and $g(B)=\mathbb E_{Z\sim D^r}G_Z(B)$. For real $L\ge8$, $t\ge1$ with $(L/4)^t\ge2(\sigma+1)$, every bank $B_g=B(X)$ of a routing $X$ of $M$ selected from the cohorts satisfies
--   $$
--   \mathbb E\,\hat g(B_g)\ \le\ L\,\mathbb E\,g(B_g)+\frac{4(t+2)P(M)}{q}.\tag{9}
--   $$
--   The point is uniformity over banks: the selected bank may depend arbitrarily on the same information it is validated on.
--
--   Differences from the source:
--   - encoding: E[· | M] with M independent of the cohorts → M fixed; reason: conditioning on M; same statement
--   - encoding: every information-selected feasible bank → B(sel(Y)) for every function sel from the cohorts to routings of M; reason: a randomized selection is a mixture of deterministic ones and both sides are linear in its law
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §3.1, Lemma 3.1, p.7, eq. (9)

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_FinLaw
import Definitions.Def_AvgValueAlloc_iidE
import Definitions.Def_AvgValueAlloc_sigmaOn
import Definitions.Def_AvgValueAlloc_posVal
import Definitions.Def_AvgValueAlloc_routBank
import Definitions.Def_AvgValueAlloc_groupSum

namespace AvgValueAlloc

/-- **Lemma 3.1 (Independent adaptive-bank validation), (9).**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §3.1, Lemma 3.1, p.7: "For g(B) = E_{Z∼D^r}G_Z(B) and L ≥ 8,
t ≥ 1 such that (L/4)^t ≥ 2(σ + 1), every information-selected feasible bank satisfies
E[ĝ(B_g) | M] ≤ LE[g(B_g) | M] + 4(t + 2)P(M)/q. (9)" Setting, p.7: "If S ≥ T, use r = ⌊T/2⌋ and
q = ⌊S/r⌋ disjoint historical cohorts Y_1, …, Y_q of size r. Set ĝ = q^{-1} Σ_b G_{Y_b}"; "Fix funding
M independently of the information cohorts"; "σ is an upper bound on the relevant positive
ambiguity".

Let `ρ > 0`, `D` a finite law, `M` fixed funding items, `σ ≥ σ_M`, `q ≥ 1` and `r` cohort
counts, and real `L ≥ 8`, `t ≥ 1` with `(L/4)^t ≥ 2(σ + 1)`. Draw `q` independent cohorts of `r`
records from `D`. For every rule selecting a routing `X` of `M` from the cohorts, with
`B_g = B(X)`, `ĝ(B) = q^{-1} Σ_b G_{Y_b}(B)` and `g(B) = E_{Z∼D^r} G_Z(B)`:
`E ĝ(B_g) ≤ L · E g(B_g) + 4(t + 2) P(M)/q`.

**Formalization Note.** `M` is fixed, which is the conditioning on `M`. The selection is an
arbitrary function of all cohorts (a randomized selection is a mixture of these). -/
theorem lemma_3_1 {n m : ℕ} (ρ : Fin n → ℚ) (hρ : ∀ j, 0 < ρ j) (D : FinLaw n) (hD : D.IsLaw)
    (M : Fin m → Vec n) (σ : ℕ) (hσ : sigmaOn ρ (Finset.univ.image M) ≤ σ) (q r : ℕ)
    (hq : 1 ≤ q) (L t : ℝ) (hL : 8 ≤ L) (ht : 1 ≤ t) (hLt : 2 * ((σ : ℝ) + 1) ≤ (L / 4) ^ t)
    (sel : (Fin q × Fin r → Vec n) → Fin m → Option (Fin n))
    (hsel : ∀ Y, IsRouting ρ M (sel Y)) :
    iidR D (Fin q × Fin r) (fun Y =>
        (1 / (q : ℝ)) * ∑ b : Fin q, Gdy ρ (fun i : Fin r => Y (b, i)) (routBank ρ M (sel Y))) ≤
      L * iidR D (Fin q × Fin r) (fun Y =>
          iidR D (Fin r) (fun Z => Gdy ρ Z (routBank ρ M (sel Y)))) +
        4 * (t + 2) * posValSum ρ M / q := by sorry

end AvgValueAlloc
