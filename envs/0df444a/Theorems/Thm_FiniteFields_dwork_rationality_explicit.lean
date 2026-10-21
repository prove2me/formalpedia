-- Prove2me | Theorems.Thm_FiniteFields_dwork_rationality_explicit
-- name    : FiniteFields.dwork_rationality_explicit
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T02:04:33.840291+00:00
-- url     : https://prove2.me/theorems/b922d788-9fd3-4a26-8fa7-35f4bcab468b
-- title:
--   Dwork's rationality theorem: the zeta function of a separated scheme of finite type over $\mathbb{F}_q$ is $P/Q$ with $Q(0)=1$ and $P, Q$ coprime
-- statement:
--   **Setting.** Let $k$ be a finite field with $q$ elements and characteristic $p$, and for every $s \ge 1$ fix an extension $\mathbb{F}_{q^s}$ of $k$ of degree $s$. Let $X$ be a scheme with a structure morphism $\pi : X \to \operatorname{Spec} k$, and assume that
--
--   - $\pi$ is of **finite type** (locally of finite type and quasi-compact), and
--   - $\pi$ is **separated**.
--
--   For $s \ge 1$ let
--   $$N_s = \# X(\mathbb{F}_{q^s})$$
--   be the number of $\mathbb{F}_{q^s}$-points of $X$ over $k$, i.e. of morphisms of schemes $x : \operatorname{Spec} \mathbb{F}_{q^s} \to X$ with $\pi \circ x = \operatorname{Spec}(k \hookrightarrow \mathbb{F}_{q^s})$; this number is finite. The **zeta function** of $X$ is the formal power series
--   $$Z(X; t) = \exp\Big(\sum_{s \ge 1} \frac{N_s}{s}\, t^s\Big) \in \mathbb{Q}[[t]].$$
--
--   **Theorem.** There exist polynomials $P, Q \in \mathbb{Q}[t]$ such that
--
--   1. $Q(0) = 1$;
--   2. $P$ and $Q$ are coprime in $\mathbb{Q}[t]$: there are $A, B \in \mathbb{Q}[t]$ with $AP + BQ = 1$;
--   3. $Z(X;t)$ is the zeta series of the counts $(N_s)$, in the sense that its constant term is $1$ and
--   $$\frac{d}{dt} Z(X; t) = \Big(\sum_{s \ge 1} N_s\, t^{s-1}\Big)\, Z(X; t),$$
--   a condition that determines $Z(X;t)$ uniquely;
--   4. $$Q(t)\, Z(X; t) = P(t) \qquad \text{in } \mathbb{Q}[[t]].$$
--
--   In other words, $Z(X;t) = P(t)/Q(t)$ is a rational function, written in lowest terms with denominator normalized by $Q(0) = 1$.
--
--   This is Dwork's theorem (1960) on the rationality of the zeta function, the first of the Weil conjectures to be proved. Dwork proves it for varieties by $p$-adic analysis and the rationality criterion of §4, and extends it to abstract varieties through a finite affine cover and inclusion–exclusion (§5, Application 2). Here it is stated for every separated scheme of finite type over $k$; $X$ need not be affine, reduced, irreducible, smooth or proper.
--
--   **Formalization Note.** Lean indexes the degree $s = n+1$ by $n \in \mathbb{N}$, and $\mathbb{F}_{q^{n+1}}$ is mathlib's `FiniteField.Extension k p (n+1)`. The count $N_{n+1}$ is `pointCount_of_finiteType k p X π hπ n`, the cardinality (`Nat.card`) of the type of $k$-morphisms $\operatorname{Spec} \mathbb{F}_{q^{n+1}} \to X$, finite by the finite-type hypothesis. The series $Z(X;t)$ is `Dwork.separatedFiniteTypeZetaSeries k p π hπ`, the formal exponential of $\sum_{n \ge 0} N_{n+1}\, t^{n+1}/(n+1)$; part 3 is the predicate `IsZetaSeries`, whose counting series is $\sum_{n \ge 0} N_{n+1} t^n$. Finite type is `Schemes.FiniteType π`, i.e. `LocallyOfFiniteType π ∧ QuasiCompact π`. The prime $p$ is an explicit parameter with `[Fact p.Prime]` and `[CharP k p]`, the field $k$ lives in `Type` (universe $0$), and `IsCoprime P Q` means $\exists\, A, B,\ AP + BQ = 1$.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §4, complement to Theorem 2 ($\zeta(V;t)$ is rational), and §5, Application 2 (extension to abstract varieties by a finite affine cover and inclusion–exclusion). Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Terminal/DworkRationality.lean`, declaration `WeilConjectures.dwork_rationality_explicit`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_Devissage

open FiniteFields
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {X : Scheme} (π : X ⟶ Spec (.of k))

theorem FiniteFields.dwork_rationality_explicit (hπ : Schemes.FiniteType π) (hsep : IsSeparated π) :
    ∃ P Q : Polynomial ℚ,
      Q.eval 0 = 1 ∧ IsCoprime P Q ∧
      IsZetaSeries (fun n ↦ pointCount_of_finiteType k p X π hπ n)
        (Dwork.separatedFiniteTypeZetaSeries k p π hπ) ∧
      (Q : PowerSeries ℚ) * Dwork.separatedFiniteTypeZetaSeries k p π hπ = (P : PowerSeries ℚ) := by sorry
