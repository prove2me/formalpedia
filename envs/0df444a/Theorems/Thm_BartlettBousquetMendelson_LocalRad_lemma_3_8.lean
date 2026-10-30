-- Prove2me | Theorems.Thm_BartlettBousquetMendelson_LocalRad_lemma_3_8
-- name    : BartlettBousquetMendelson.LocalRad.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:05:39.156552+00:00
-- url     : https://prove2.me/theorems/b93142b2-3f51-4a75-b157-1d3409d32b5e
-- title:
--   Lemma 3.8 (corrected: $\max(P_nf,\frac K{K-1}P_nf)$ in the first and third claims)
-- statement:
--   Fix a sample $X_1,\dots,X_n$. Let $\mathcal F$ be a class of functions and $T$ a functional with $0\le T(f)\le B\,Pf$ for every $f\in\mathcal F$, where $B>0$. Let $K>1$, $\lambda>1$ and $r>0$, and let $\mathcal G_r$, $\tilde{\mathcal G}_r$ be the weighted classes, with $V_r^\pm$, $\tilde V_r^\pm$ the deviations $\sup_g(Pg-P_ng)$, $\sup_g(P_ng-Pg)$ over them. Then
--
--   1. if $V_r^+\le r/(\lambda BK)$, then for all $f\in\mathcal F$, $$Pf\le\max\Big(P_nf,\frac K{K-1}P_nf\Big)+\frac r{\lambda BK};$$
--   2. if $V_r^-\le r/(\lambda BK)$, then for all $f\in\mathcal F$, $$P_nf\le\frac{K+1}KPf+\frac r{\lambda BK};$$
--   3. if $\tilde V_r^+\le r/(BK)$, then for all $f\in\mathcal F$, $$Pf\le\max\Big(P_nf,\frac K{K-1}P_nf\Big)+\frac r{BK};$$
--   4. if $\tilde V_r^-\le r/(BK)$, then for all $f\in\mathcal F$, $$P_nf\le\frac{K+1}KPf+\frac r{BK}.$$
--
--   This deterministic lemma converts a deviation bound on a rescaled class into the error bound for the original class.
--
--   Differences from the source:
--   - correction: Pf ≤ (K/(K − 1)) Pₙf + r/(λBK) (claim 1) and Pf ≤ (K/(K − 1)) Pₙf + r/(BK) (claim 3) → max(Pₙf, K/(K − 1)·Pₙf) in place of (K/(K − 1))·Pₙf; reason: false when Pₙf < 0: X = {0,1}, P uniform, F = {f}, f(0) = 3, f(1) = −1, T = Var (T f = 4), B = 4, n = 1, sample X₁ = 1 (Pₙf = −1), K = 2; claim 1 with λ = 2, r = 32: G_r = {f}, V⁺ = 2 = r/(λBK) but K/(K−1)Pₙf + r/(λBK) = 0 < 1 = Pf; claim 3 with r = 16: G̃_r = {f}, Ṽ⁺ = 2 = r/(BK), same failure; the max equals the printed term whenever Pₙf ≥ 0
--   - reading: Fix K > 1, λ > 0 → λ > 1; reason: the notation the lemma uses (p. 14: "Given a class F, λ > 1 and r > 0, let w(f) = …") requires λ > 1; for λ ≤ 1, w(f) does not exist when T(f) > r
--   - encoding: V ≤ c for V a supremum over the class → every deviation over the class is ≤ c; reason: the meaning of a bound on a supremum; it needs no boundedness assumption on the class
--   - encoding: T : F → ℝ⁺ → T : (X → ℝ) → ℝ with 0 ≤ T f for f ∈ F; reason: T is only evaluated on F
--   - encoding: the deviations as random quantities → one fixed sample ω : Fin n → X, 0 < n; reason: the lemma is deterministic in the sample
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), Lemma 3.8, pp. 14–15 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_empMean
import Definitions.Def_BartlettBousquetMendelson_LocalRad_weightedClass
import Definitions.Def_BartlettBousquetMendelson_LocalRad_tildeClass

open MeasureTheory

namespace BartlettBousquetMendelson.LocalRad

/-- **Lemma 3.8 (corrected: max(Pₙf, K/(K−1)Pₙf) in the first and third claims).**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), Lemma 3.8, pp. 14–15: "With the above notation, assume that there is a constant B > 0 such
that for every f ∈ F, T(f) ≤ BPf. Fix K > 1, λ > 0 and r > 0. If V+r ≤ r/(λBK), then
∀f ∈ F Pf ≤ (K/(K − 1)) Pnf + r/(λBK). Also, if V−r ≤ r/(λBK), then
∀f ∈ F Pnf ≤ ((K + 1)/K) Pf + r/(λBK). Similarly, if K > 1 and r > 0 are such that
Ṽ+r ≤ r/(BK), then ∀f ∈ F Pf ≤ (K/(K − 1)) Pnf + r/(BK). Also, if Ṽ−r ≤ r/(BK), then
∀f ∈ F Pnf ≤ ((K + 1)/K) Pf + r/(BK)."
The notation (p. 14): "Given a class F, λ > 1 and r > 0, let w(f) = min{rλ^k : k ∈ N,
rλ^k ≥ T(f)} and set Gr = {(r/w(f)) f : f ∈ F}"; "V+r = sup_{g∈Gr} Pg − Png and
V−r = sup_{g∈Gr} Png − Pg"; "G̃r := {rf/(T(f) ∨ r) : f ∈ F}", Ṽ±r likewise over G̃r.

Deterministic: for one fixed sample `ω`, a nonnegative functional `T` with `T f ≤ B Pf` on `F`
(`B > 0`), and `K > 1`, `λ > 1`, `r > 0`:
(1) if `Pg − Pₙg ≤ r/(λBK)` for all `g ∈ G_r`, then `Pf ≤ max(Pₙf, K/(K−1) Pₙf) + r/(λBK)`
for all `f ∈ F`; (2) if `Pₙg − Pg ≤ r/(λBK)` for all `g ∈ G_r`, then
`Pₙf ≤ (K+1)/K Pf + r/(λBK)` for all `f ∈ F`; (3), (4) the same over `G̃_r` with `r/(BK)`.

**Formalization Note.** Correction (claims 1 and 3): the printed `K/(K−1) Pₙf` is replaced by
`max(Pₙf, K/(K−1) Pₙf)`, which equals it whenever `Pₙf ≥ 0`. Counterexample to the printed
claims: `X = {0, 1}` with `P` uniform, `F = {f}`, `f(0) = 3`, `f(1) = −1` (`Pf = 1`), `T = Var`
(`T f = 4`), `B = 4`, `n = 1`, sample `X₁ = 1` (`Pₙf = −1`), `K = 2`. Claim 1 with `λ = 2`,
`r = 32`: `w(f) = 32`, `G_r = {f}`, `V⁺ = 2 = r/(λBK)`, but `K/(K−1)Pₙf + r/(λBK) = 0 < 1`.
Claim 3 with `r = 16`: `G̃_r = {f}`, `Ṽ⁺ = 2 = r/(BK)`, same failure. "`V ≤ c`" is written
"every deviation over the class is `≤ c`", which is the meaning of a supremum bound and needs no
boundedness assumption. Reading λ: `λ > 1`, as in the notation the lemma uses (for `λ ≤ 1`, `w(f)`
does not exist when `T(f) > r`); the lemma's "λ > 0" is read as `λ > 1`. `T : F → ℝ⁺` is a
functional on all of `X → ℝ`, nonnegative on `F`. -/
theorem lemma_3_8 {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (F : Set (X → ℝ)) (T : (X → ℝ) → ℝ) (B : ℝ) (n : ℕ) (hn : 0 < n) (ω : Fin n → X)
    (hB : 0 < B) (hT0 : ∀ f ∈ F, 0 ≤ T f) (hTB : ∀ f ∈ F, T f ≤ B * ∫ y, f y ∂P) :
    ∀ K lam r : ℝ, 1 < K → 1 < lam → 0 < r →
      ((∀ g ∈ weightedClass F T r lam, ∫ y, g y ∂P - empMean n g ω ≤ r / (lam * B * K)) →
        ∀ f ∈ F, ∫ y, f y ∂P ≤
          max (empMean n f ω) (K / (K - 1) * empMean n f ω) + r / (lam * B * K)) ∧
      ((∀ g ∈ weightedClass F T r lam, empMean n g ω - ∫ y, g y ∂P ≤ r / (lam * B * K)) →
        ∀ f ∈ F, empMean n f ω ≤ (K + 1) / K * ∫ y, f y ∂P + r / (lam * B * K)) ∧
      ((∀ g ∈ tildeClass F T r, ∫ y, g y ∂P - empMean n g ω ≤ r / (B * K)) →
        ∀ f ∈ F, ∫ y, f y ∂P ≤
          max (empMean n f ω) (K / (K - 1) * empMean n f ω) + r / (B * K)) ∧
      ((∀ g ∈ tildeClass F T r, empMean n g ω - ∫ y, g y ∂P ≤ r / (B * K)) →
        ∀ f ∈ F, empMean n f ω ≤ (K + 1) / K * ∫ y, f y ∂P + r / (B * K)) := by sorry

end BartlettBousquetMendelson.LocalRad
