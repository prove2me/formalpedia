-- Prove2me | Theorems.Thm_BoolCSPDel_Supplement_theorem_4_2
-- name    : BoolCSPDel.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:07:29.532194+00:00
-- url     : https://prove2.me/theorems/fbf72e74-9acf-4a2b-ae18-92c6a136906c
-- title:
--   Theorem 4.2 — sketches deciding $\mathrm{CSP}(R)$ need $\Omega_k(n^d)$ bits, on instances with distinct variables in every scope
-- statement:
--   Fix $k\ge 0$ and let $R$ be a Boolean relation of arity at most $k$ that is **nonempty** and **not constant-satisfiable** (neither the all-zeros nor the all-ones tuple lies in $R$). Let $d=\deg_{\mathbb Z}(R)$ be its integer capturing degree, the least degree of an integer polynomial vanishing exactly on $R$. An instance of $\mathrm{CSP}(R)$ on $n$ variables is a frequency vector $f$ over the constraint types $C=(R,\text{ordered scope})$; $C$ is active when $f(C)>0$, and $\mathrm{Sat}(f)$ is the set of assignments satisfying every active constraint.
--
--   There are constants $c>0$, $F$ and $N_0$, depending only on $k$, such that for every such $R$ and every $n\ge N_0$ there is a probability distribution $\mathcal D$ on instances over $n$ variables with the following properties:
--
--   1. every instance in the support of $\mathcal D$ has all frequencies in $\{0,1,\dots,F\}$;
--   2. every active constraint of every instance in the support of $\mathcal D$ has **pairwise distinct variables** in its scope;
--   3. every public-coin linear sketch (seed $\omega\sim\mu$, homomorphism $L_\omega$ into a finite abelian group, decoder) that decides whether $\mathrm{Sat}(f)\neq\emptyset$ with average error at most $1/3$ over $\omega\sim\mu$ and $f\sim\mathcal D$ has size
--   $$B=\sup_\omega \log_2|\operatorname{im}L_\omega|\ \ge\ c\,n^{d}.$$
--
--   The distribution is fixed before the sketch. This is the sketching half of the paper's streaming lower bound: combined with the strict-turnstile streaming-to-sketching reduction (Theorem 4.3) it yields the $\Omega_k(n^d/\log n)$-bit streaming lower bound of Theorem 4.1. The distinct-variables property is what lets the hard instances be built in models that forbid repeated variables in a scope.
--
--   **Formalization Note** The relation is `R : Rel k` (arity at most $k$) and the language is $\{R\}$. The average-error condition is encoded by measurable events $A_f$ contained in the sets of seeds on which the decoder is correct for $f$, with $\sum_f \mathcal D(f)\,\mu(A_f)\ge 2/3$. "Distinct variables within its scope" is injectivity of the scope map of each active constraint.
--
--   Differences from the source:
--   - generalization: the relation R has arity k, and the constant F_R and the implicit constants of Ω_k(n^d) and "sufficiently large n" may depend on R → R has arity at most k, and c, F, N₀ are chosen before R and depend only on k; reason: there are finitely many relations of arity at most k, so uniform constants exist exactly when per-relation ones do, and the Lean statement specializes to the printed one at any fixed R of arity k
--   - encoding: Ω_k(n^d) → an explicit constant c > 0 with c · n^d ≤ B for all n ≥ N₀; reason: Lean has no asymptotic notation; this is the meaning of Ω_k for sufficiently large n
--   - encoding: sketch deciding satisfiability with average error at most 1/3 → measurable events A f inside the seed sets on which the decoder is correct for f, with Σ_f D(f) μ(A f) ≥ 2/3; reason: the success set need not be measurable for an arbitrary decoder; the measurable-subset form is the inner-measure reading of "success probability at least 2/3", the same encoding as the published Corollary 4.15
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519db632914d55b4bfaf996a5fa47293f23b2596fd69a57fefa11a05d6e), Theorem 4.2, p.24 (restated with proof, p.28)

import Mathlib
import Definitions.Def_BoolCSPDel_degZ
import Definitions.Def_BoolCSPDel_Con
import Definitions.Def_BoolCSPDel_Sketch

open MeasureTheory

namespace BoolCSPDel.Supplement

/-- **Theorem 4.2 (Sketching lower bound).** Bandekar, Sharma, Velusamy, *A New Characterization of
Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256
15f83519…), Theorem 4.2, p.24 (restated with proof on p.28).

For a nonempty, non-constant-satisfiable Boolean relation `R` with `d = deg_ℤ(R)` there is a constant
`F` such that for every large `n` there is one distribution on instances over `n` variables with
frequencies in `[0, F]`, in which every active constraint has pairwise distinct variables in its
scope, such that **every** public-coin linear sketch deciding satisfiability with average error at
most `1/3` has size at least `c · n^d`.

**Formalization Note.** `R : Rel k` has arity at most `k` and the instance language is `{R}`. A
nonempty non-constant-satisfiable relation is automatically proper, so no further hypothesis is
added. The constants `c`, `F`, `N₀` are chosen before `R` and depend on `k` only; since there are
finitely many relations of arity at most `k`, this specializes to the printed per-relation
constants. The distribution comes first and the sketch after it. Average error is over the seed and
the instance, encoded by measurable events `A f` inside the success sets with
`Σ_f D(f) μ(A f) ≥ 2/3`. "Distinct variables within its scope" is injectivity of the scope map
`C.2 : Fin a → Fin n` for every constraint type `C` active (`0 < f C`) in an instance `f` of the
support of the distribution. -/
theorem theorem_4_2 (k : ℕ) : ∃ (c : ℝ) (F N₀ : ℕ), 0 < c ∧
    ∀ R : Rel k, R.2.Nonempty → ¬ ConstSat ({R} : Lang k) → ∀ n, N₀ ≤ n →
      ∃ D : PMF (Con ({R} : Lang k) (Fin n) → ℤ),
        (∀ f ∈ D.support, ∀ C, 0 ≤ f C ∧ f C ≤ F) ∧
        (∀ f ∈ D.support, ∀ C, 0 < f C → Function.Injective C.2) ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (σ : Sketch (Con ({R} : Lang k) (Fin n)) Ω Bool)
          (A : (Con ({R} : Lang k) (Fin n) → ℤ) → Set Ω),
          (∀ f, MeasurableSet (A f)) →
          (∀ f, A f ⊆ {ω | σ.out ω f = true ↔ (Sat f).Nonempty}) →
          (2 / 3 : ENNReal) ≤ ∑' f, D f * μ (A f) →
          ∀ B : ℝ, σ.HasSize B → c * (n : ℝ) ^ degZ R ≤ B := by sorry

end BoolCSPDel.Supplement
