-- Prove2me | Theorems.Thm_AC02Frege_Supplement_theorem_6_3
-- name    : AC02Frege.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:59:08.674914+00:00
-- url     : https://prove2.me/theorems/a0c85e23-496a-43d4-a589-08268df17aa7
-- title:
--   Theorem 6.3 (corrected: $T$ counted as at least $1$) — restricting a small $\mathrm{Res}(\mathrm{PC})$ refutation to low degree
-- statement:
--   Let $F'$ be a CNF on $n'\ge2$ variables, let $d\ge2$ and $q\ge2$, and let $\Pi$ be a $\mathrm{Res}(\mathrm{PC})$ refutation of the selector substitution $F'\circ\mathrm{Sel}_q$, with no bound on the degree of its polynomials, of total size $T$. Then, for an absolute constant $C>0$:
--
--   1. with probability at least $1-Tq^{-d}$ over the choice of a random selector restriction $\rho$, every polynomial of $\Pi|_\rho$ has degree less than $d$, and $\Pi|_\rho$ can be completed to a $\mathrm{Res}(\mathrm{PC}_{2d})$ refutation of $F'$ with at most $T(n')^{Cd}$ lines;
--   2. in particular, if every $\mathrm{Res}(\mathrm{PC}_{2d})$ refutation of $F'$ has at least $L$ lines, then
--   $$
--   T\ \ge\ \min\Bigl\{q^d,\ \frac{L}{(n')^{Cd}}\Bigr\}. \tag{43}
--   $$
--
--   Here $\Pi|_\rho$ replaces every polynomial $u$ of $\Pi$ by $\mathrm{ML}(u|_\rho)$, and "completed" means that the refutation contains every line of $\Pi|_\rho$. The theorem transfers line lower bounds for bounded-degree $\mathrm{Res}(\mathrm{PC})$ to total-size lower bounds for $\mathrm{Res}(\mathrm{PC})$ of unbounded degree; it is the step from Theorem 4.20 to Theorem 1.5.
--
--   **Formalization Note** The total size is floored at $1$ (see the correction below); this only matters when $F'$ contains the empty clause.
--
--   Differences from the source:
--   - correction: total size T = the number of monomial occurrences (Definition 2.7, which also asserts S ≤ T) → T = totalSize π = max 1 (number of monomial occurrences); reason: if F′ contains the empty clause, Π = [∅] (the input clause ∅^Sel = ∅) is a Res(PC) refutation of F′ ∘ Sel_q with T = 0, and the printed conclusions (a completion with at most 0·(n′)^{Cd} lines; T ≥ min{q^d, L/(n′)^{Cd}} > 0 with L = 1) fail; every refutation with a monomial occurrence is unchanged
--   - reading: lines as disjunctions of equations, contraction a rule → lines as finite sets of polynomials, in Π, in Π|ρ and in the completed refutation; reason: order and repetition of the equations of a disjunction are immaterial (weakening and contraction are rules); the restriction acts polynomial by polynomial
--   - encoding: F′ a CNF on n′ ≥ 2 variables → F′ : CNF V for a finite type V with 2 ≤ card V; n′ = card V; reason: same instances
--   - encoding: "with probability at least 1 − Tq^{−d} over the choice of a random selector restriction ρ" → (1 − T/q^d) · q^{2n′} ≤ #{A : V → Bool → Fin q good}; reason: ρ is uniform over the q^{2n′} column choices
--   - reading: "Π|ρ can be completed to a Res(PC_2d) refutation of F′ with at most T(n′)^{Cd} lines" → there is a Res(PC_2d) refutation of F′ with at most T(n′)^{Cd} lines that contains every line of Π|ρ; reason: 'completed' keeps the restricted lines and inserts the derivations that repair the multiplication steps (Step 2); this is stronger than the bare existence of a short refutation
--   - encoding: "for an absolute constant C"; (43) "if every Res(PC_2d) refutation of F′ has at least L lines" → ∃ C > 0 before V, F′, d, q, Π, used in both conclusions; ∀ L : ℕ, (∀ refutations πr, L ≤ |πr|) → min{q^d, L/(n′)^{Cd}} ≤ T (real powers); reason: same statement
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Theorem 6.3, p.33 (proof p.34); Definitions 6.1, 6.2, pp.33–34; Definition 2.7, p.11

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_Supplement_ResPC
import Definitions.Def_AC02Frege_Supplement_selector

namespace AC02Frege.Supplement

open LiftSAParity Classical

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower
Bounds*, manuscript (sha256 88d149fa…), Theorem 6.3, p.33 (restricting a small refutation to low
degree). Let `F′` be a CNF on `n′ ≥ 2` variables, let `d ≥ 2` and `q ≥ 2`, and let `π` be a
`Res(PC)` refutation of `F′ ∘ Sel_q`, with no bound on the degree of its polynomials, of total size
`T`. Then with probability at least `1 − Tq^{−d}` over the choice of a random selector restriction
`ρ`, every polynomial of `π|_ρ` has degree less than `d`, and `π|_ρ` can be completed to a
`Res(PC_{2d})` refutation of `F′` with at most `T(n′)^{Cd}` lines, for an absolute constant `C`. In
particular, if every `Res(PC_{2d})` refutation of `F′` has at least `L` lines, then
`T ≥ min{q^d, L/(n′)^{Cd}}` (43).

**Formalization Note** The variables of `F′` are a finite type `V` with `n′ = |V|`. A selector
restriction is a choice of columns `A : V → Bool → Fin q`, uniform over all `q^{2n′}` choices, so
"with probability at least `p`" is `#{A good} ≥ p · q^{2n′}`. `π|_ρ` replaces each polynomial `u` by
`ML(u|_ρ)`; "can be completed" is read as: there is a `Res(PC_{2d})` refutation of `F′` with at most
`T(n′)^{Cd}` lines that contains every line of `π|_ρ`. `T` is `totalSize` (monomial occurrences,
floored at `1`). This floor is a correction: if `F′` contains the empty clause, `π = [∅]` refutes
`F′ ∘ Sel_q` with no monomial occurrence, and the printed statement (a completion with at most
`0 · (n′)^{Cd}` lines) fails. The single constant `C` is chosen before everything else and serves both the line
count and (43). -/
theorem theorem_6_3 :
    ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (F' : CNF V) (d q : ℕ),
      2 ≤ Fintype.card V → 2 ≤ d → 2 ≤ q →
      ∀ π : List (RLine (V × Bool × Fin q)), IsResRefutation ⊤ (selSubst F' q) π →
        (1 - (totalSize π : ℝ) / (q : ℝ) ^ d) * (q : ℝ) ^ (2 * Fintype.card V) ≤
          ((Finset.univ.filter (fun A : V → Bool → Fin q =>
            (∀ L ∈ π, ∀ u ∈ L, (restrictPoly A u).totalDegree < d) ∧
            ∃ πr : List (RLine V), IsResRefutation ((2 * d : ℕ) : ℕ∞) F' πr ∧
              (∀ L ∈ π, restrictLine A L ∈ πr) ∧
              (πr.length : ℝ) ≤ totalSize π * (Fintype.card V : ℝ) ^ (C * d))).card : ℝ) ∧
        ∀ L : ℕ, (∀ πr : List (RLine V), IsResRefutation ((2 * d : ℕ) : ℕ∞) F' πr →
            L ≤ πr.length) →
          min ((q : ℝ) ^ d) ((L : ℝ) / (Fintype.card V : ℝ) ^ (C * d)) ≤ totalSize π := by sorry

end AC02Frege.Supplement
