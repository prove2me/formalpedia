-- Prove2me | Theorems.Thm_BartlettBousquetMendelson_LocalRad_theorem_3_3_part_2
-- name    : BartlettBousquetMendelson.LocalRad.theorem_3_3_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:06:26.124994+00:00
-- url     : https://prove2.me/theorems/931e5bdb-5a6c-491a-a034-270a3d142e1d
-- title:
--   Theorem 3.3, part 2 (corrected: $\max(P_nf,\frac K{K-1}P_nf)$ in the first claim)
-- statement:
--   Let $X_1,\dots,X_n$ be iid with law $P$ ($n\ge1$). Let $\mathcal F$ be a class of measurable functions with ranges in $[a,b]$, $T$ a functional and $B>0$ a constant such that for every $f\in\mathcal F$ and $\alpha\in[0,1]$
--
--   $$
--   \mathrm{Var}[f]\le T(f)\le B\,Pf,\qquad T(\alpha f)\le\alpha^2T(f).
--   $$
--
--   Let $\psi$ be a nontrivial sub-root function with fixed point $r^*>0$, and assume that for every $r\ge r^*$
--
--   $$
--   \psi(r)\ge B\,\mathbb ER_n\{f\in\mathrm{star}(\mathcal F,0):T(f)\le r\}.
--   $$
--
--   Then for every $K>1$ and every $x>0$:
--
--   1. with probability at least $1-e^{-x}$, for all $f\in\mathcal F$,
--   $$
--   Pf\le\max\Big(P_nf,\frac K{K-1}P_nf\Big)+\frac{6K}Br^*+\frac{x\,(11(b-a)+5BK)}n;
--   $$
--   2. with probability at least $1-e^{-x}$, for all $f\in\mathcal F$,
--   $$
--   P_nf\le\frac{K+1}KPf+\frac{6K}Br^*+\frac{x\,(11(b-a)+5BK)}n.
--   $$
--
--   These are the paper's error bounds with local complexity: the complexity term is the fixed point $r^*$ of a sub-root bound on local Rademacher averages over the star-hull, with the constants $c_1=6$, $c_2=5$.
--
--   Differences from the source:
--   - correction: Pf ≤ (K/(K − 1)) Pₙf + (c₁K/B) r* + x(11(b − a) + c₂BK)/n (first claim) → max(Pₙf, K/(K − 1)·Pₙf) in place of (K/(K − 1))·Pₙf; reason: false when Pₙf < 0: X = {0,1}, P uniform, F = {f}, f(0) = 3, f(1) = −1 (a = −1, b = 3), T = Var_P, B = 4, ψ(r) = min(4, 2√r), r* = 4, n = 1, K = 1.01, x = 0.7; E R₁ star(F,0) = 1 so ψ(r) = 4 = B·1 for r ≥ 4; on {X₁ = 1} (probability 1/2) the printed right side is −50 < 1 = Pf, so the claim holds with probability 1/2 < 1 − e^{−0.7}; the max equals the printed term whenever Pₙf ≥ 0
--   - reading: the measurability convention of p. 7 ("we assume that the class F and the distribution P satisfy appropriate (mild) conditions for measurability of this supremum") → each f ∈ F measurable, IsPointwiseMeasurableClass F, and for every r ≥ r* the empirical Rademacher average of {g ∈ star(F,0) : T g ≤ r} a.e.-strongly measurable in the sample; reason: the paper leaves the convention open (refs [11, 28]); pointwise measurability (van der Vaart–Wellner §2.3.3) is a standard choice that makes every supremum over the class a countable one, and Lean integrates non-measurable functions to 0
--   - generalization: T : F → ℝ⁺ (evaluated on star(F,0) in part 2) → T : (X → ℝ) → ℝ constrained only by Var f ≤ T f ≤ B·Pf and T(αf) ≤ α²T(f) for f ∈ F, α ∈ [0,1]; reason: every T of the paper extends to such a functional; nonnegativity on F follows from Var ≤ T
--   - encoding: some constant B → 0 < B; reason: the conclusion divides by B; Lemma 3.8 (p. 14) states B > 0
--   - encoding: ψ a sub-root function with fixed point r* → IsNontrivialSubRoot ψ, 0 < r*, ψ r* = r*; reason: the paper only considers nontrivial sub-root functions (p. 9); r* is unique by Lemma 3.2
--   - reading: part 2: "If, in addition, … and if ψ satisfies, for any r ≥ r*, ψ(r) ≥ BERn{f ∈ star(F,0) : T(f) ≤ r}" → part 1's hypothesis on ψ is not repeated; reason: part 2's hypothesis implies part 1's because F ⊆ star(F,0); "in addition" refers to the condition T(αf) ≤ α²T(f)
--   - encoding: X₁, …, Xₙ independent with law P, independent Rademacher signs → sample ω : Fin n → X under Measure.pi (fun _ => P), signs averaged exactly over Fin n → Bool, 0 < n; reason: the statement depends only on the law of the sample; n ≥ 1 is implicit in 1/n
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), Theorem 3.3, part 2, p. 10 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_empMean
import Definitions.Def_BartlettBousquetMendelson_LocalRad_empRademacher
import Definitions.Def_BartlettBousquetMendelson_LocalRad_rademacherAvg
import Definitions.Def_BartlettBousquetMendelson_LocalRad_starHull
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsNontrivialSubRoot
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass

open MeasureTheory ProbabilityTheory

namespace BartlettBousquetMendelson.LocalRad

/-- **Theorem 3.3, part 2 (corrected: max(Pₙf, K/(K−1)Pₙf) in the first claim).**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), Theorem 3.3, p. 10: "Let F be a class of functions with ranges in [a,b] and assume that there
are some functional T : F → R+ and some constant B such that for every f ∈ F,
Var[f] ≤ T(f) ≤ BPf. Let ψ be a sub-root function and let r∗ be the fixed point of ψ.
1. Assume that ψ satisfies, for any r ≥ r∗, ψ(r) ≥ BERn{f ∈ F : T(f) ≤ r}. Then, with c1 = 704
and c2 = 26, for any K > 1 and every x > 0, with probability at least 1 − e^{−x},
∀f ∈ F Pf ≤ (K/(K − 1)) Pnf + (c1K/B) r∗ + x(11(b − a) + c2BK)/n. Also, with probability at
least 1 − e^{−x}, ∀f ∈ F Pnf ≤ ((K + 1)/K) Pf + (c1K/B) r∗ + x(11(b − a) + c2BK)/n.
2. If, in addition, for f ∈ F and α ∈ [0,1], T(αf) ≤ α^2T(f), and if ψ satisfies, for any
r ≥ r∗, ψ(r) ≥ BERn{f ∈ star(F,0) : T(f) ≤ r}, then the same results hold true with c1 = 6 and
c2 = 5."

Let `X₁, …, Xₙ` (`n ≥ 1`) be iid `P`, `F` a class of measurable functions with ranges in
`[a, b]`, `T` a functional and `B > 0` with `Var f ≤ T f ≤ B Pf` and `T(α f) ≤ α² T(f)` for
`f ∈ F`, `α ∈ [0, 1]`. Let `ψ` be a nontrivial sub-root function with fixed point `r* > 0` such
that `ψ(r) ≥ B E Rₙ {g ∈ star(F, 0) : T g ≤ r}` for every `r ≥ r*`. Then for every `K > 1` and
`x > 0`: (1) with probability at least `1 − e^{−x}`, for all `f ∈ F`,
`Pf ≤ max(Pₙf, K/(K−1) Pₙf) + 6K r*/B + x(11(b − a) + 5BK)/n`; (2) with probability at least
`1 − e^{−x}`, for all `f ∈ F`, `Pₙf ≤ (K+1)/K Pf + 6K r*/B + x(11(b − a) + 5BK)/n`.

**Formalization Note.** Correction (first claim): the printed `K/(K−1) Pₙf` is replaced by
`max(Pₙf, K/(K−1) Pₙf)`, identical whenever `Pₙf ≥ 0`. Counterexample to the printed claim
(every hypothesis holds): `X = {0, 1}`, `P` uniform, `F = {f}`, `f(0) = 3`, `f(1) = −1`
(`a = −1`, `b = 3`), `T = Var_P`, `B = 4`, `ψ(r) = min(4, 2√r)`, `r* = 4`, `n = 1`,
`K = 1.01`, `x = 0.7`; then `E R₁ star(F, 0) = 1`, and on `{X₁ = 1}` (probability `1/2`) the
printed right side is `−50 < 1 = Pf`, so the claim holds with probability `1/2 < 1 − e^{−0.7}`.
The constants `c₁ = 6`, `c₂ = 5`, `11(b − a)` are the printed ones. Readings:
(M) measurability, p. 7: each `f ∈ F` measurable, `F` pointwise measurable, and the empirical
Rademacher average of each local set `{g ∈ star(F, 0) : T g ≤ r}`, `r ≥ r*`, a.e.-strongly
measurable in the sample (otherwise Lean's integral would be `0` and the hypothesis on `ψ` empty);
(T) `T` is a functional on all of `X → ℝ` constrained only by the hypotheses above (the paper's
`T : F → ℝ⁺` is evaluated on `star(F, 0)` in part 2; nonnegativity on `F` follows from
`Var ≤ T`); (B) `B > 0`; (ψ) `r*` is any `r* > 0` with `ψ r* = r*`, unique by Lemma 3.2;
(S) the sample is `ω : Fin n → X` under `Measure.pi`, the signs averaged exactly. Part 1's
hypothesis on `ψ` is implied by part 2's (`F ⊆ star(F, 0)`) and is not repeated. -/
theorem theorem_3_3_part_2 {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P]
    (F : Set (X → ℝ)) (a b B : ℝ) (T : (X → ℝ) → ℝ) (ψ : ℝ → ℝ) (rstar : ℝ) (n : ℕ)
    (hn : 0 < n)
    (hmeas : ∀ f ∈ F, Measurable f) (hpm : IsPointwiseMeasurableClass F)
    (hrange : ∀ f ∈ F, ∀ y, f y ∈ Set.Icc a b)
    (hB : 0 < B)
    (hVarT : ∀ f ∈ F, variance f P ≤ T f) (hTB : ∀ f ∈ F, T f ≤ B * ∫ y, f y ∂P)
    (hTscale : ∀ f ∈ F, ∀ α ∈ Set.Icc (0 : ℝ) 1, T (α • f) ≤ α ^ 2 * T f)
    (hψ : IsNontrivialSubRoot ψ) (hr0 : 0 < rstar) (hfix : ψ rstar = rstar)
    (hlocmeas : ∀ r, rstar ≤ r → AEStronglyMeasurable
        (empRademacher n {g | g ∈ starHull F 0 ∧ T g ≤ r}) (Measure.pi fun _ : Fin n => P))
    (hψloc : ∀ r, rstar ≤ r → B * rademacherAvg P n {g | g ∈ starHull F 0 ∧ T g ≤ r} ≤ ψ r) :
    ∀ K x : ℝ, 1 < K → 0 < x →
      1 - Real.exp (-x) ≤ (Measure.pi fun _ : Fin n => P).real {ω | ∀ f ∈ F,
          ∫ y, f y ∂P ≤ max (empMean n f ω) (K / (K - 1) * empMean n f ω)
            + 6 * K / B * rstar + x * (11 * (b - a) + 5 * B * K) / n} ∧
      1 - Real.exp (-x) ≤ (Measure.pi fun _ : Fin n => P).real {ω | ∀ f ∈ F,
          empMean n f ω ≤ (K + 1) / K * ∫ y, f y ∂P
            + 6 * K / B * rstar + x * (11 * (b - a) + 5 * B * K) / n} := by sorry

end BartlettBousquetMendelson.LocalRad
