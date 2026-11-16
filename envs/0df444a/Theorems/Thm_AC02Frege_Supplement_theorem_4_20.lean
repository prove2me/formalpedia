-- Prove2me | Theorems.Thm_AC02Frege_Supplement_theorem_4_20
-- name    : AC02Frege.Supplement.theorem_4_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:58:21.100765+00:00
-- url     : https://prove2.me/theorems/4dc2b03e-4078-4666-9ae3-eac478641601
-- title:
--   Theorem 4.20 — majority extension with variable block length: $\log S\ge c_1(n/r)e^{-Cr/\sqrt\ell}$
-- statement:
--   Fix $0<c<1$ and a positive integer $w$. There are constants $\ell_0,\kappa,c_1,C>0$, depending only on $c,w$, with the following property. Let $F_n$ be an unsatisfiable polynomial-size CNF on $n$ variables of width at most $w$ with no PC refutation over $\mathbb F_2$ of degree $D=\lfloor cn\rfloor$. Let $\ell\ge\ell_0$ be odd and $r\ge1$ an integer with $r+\ell\le\kappa n$. Then for all sufficiently large $n$, every $S$-line syntactic $\mathrm{Res}(\mathrm{PC}_r)$ refutation of $G_n=F_n\circ\mathrm{Maj}_\ell$ satisfies
--   $$
--   \log S\ \ge\ c_1\,\frac nr\,\exp\Bigl(-C\frac{r}{\sqrt\ell}\Bigr). \tag{36}
--   $$
--   The formula $G_n$ has $N=n\ell$ variables, width at most $w(\ell+1)/2$, and $\log|G_n|=O(\ell+\log n)$. Hence the bound on lines, and a fortiori on total size, is superpolynomial in $|G_n|$ whenever
--   $$
--   \frac nr\exp\Bigl(-C\frac r{\sqrt\ell}\Bigr)=\omega(\ell+\log n). \tag{37}
--   $$
--
--   Precisely: for all $0<c<1$ and $w\ge1$ there are $\ell_0,\kappa,c_1,C>0$ such that for all exponents $k,k'$ there are $n_0,C',M$ such that for every $n\ge n_0$, every unsatisfiable CNF $F$ on $n$ variables with $|F|\le n^k$, width at most $w$ and no PC refutation of degree $\lfloor cn\rfloor$, and every odd $\ell\ge\ell_0$:
--
--   1. $2\,w(G)\le w(\ell+1)$ and $\log|G|\le C'(\ell+\log n)$ for $G=F\circ\mathrm{Maj}_\ell$;
--   2. for every integer $r\ge1$ with $r+\ell\le\kappa n$ and every $\mathrm{Res}(\mathrm{PC}_r)$ refutation of $G$ with $S$ lines and total size $T$: (36) holds, and if $(n/r)\exp(-Cr/\sqrt\ell)\ge M(\ell+\log n)$ then $|G|^{k'}\le S$ and $|G|^{k'}\le T$.
--
--   Unlike Theorem 3.14, the decay is $e^{-O(r/\sqrt\ell)}$ instead of $(D/16n)^r$, which allows degrees $r$ up to about $\sqrt\ell\log n$.
--
--   **Formalization Note** $G=F\circ\mathrm{Maj}_\ell$ is the base `lift F ℓ` and $|G|$ its `encLength` (literal occurrences plus one per clause).
--
--   Differences from the source:
--   - generalization: lines as disjunctions of equations, with weakening and contraction as rules → lines as finite sets of polynomials (RLine), contraction and reordering built in; reason: each line of a refutation in the paper's form maps to its set of polynomials, and every rule application maps to a rule application, so a paper refutation gives a set-based one with the same number of lines (and the same total size); the lower bound for set-based refutations specializes to the source
--   - encoding: "no PC refutation of degree D = ⌊cn⌋" → ¬ PCDerivable F ⌊c n⌋₊ 1 (base definition: formal degree, Boolean axioms y_i² + y_i); reason: formal degrees are integers, so degree ≤ cn means degree ≤ ⌊cn⌋; same instances
--   - reading: "Let F_n be a polynomial-size CNF" → for every exponent k, encLength F ≤ n^k, with n₀, C′, M chosen after k; reason: polynomial size means a fixed polynomial bound; ℓ₀, κ, c₁, C are chosen before k, as the theorem says they depend only on c, w
--   - reading: "Then for all sufficiently large n" → ∃ n₀ after c, w, k, k′ and before F, ℓ, r (one threshold for all ℓ, r with r + ℓ ≤ κn); reason: the stronger of the two readings; the proof's largeness conditions (D ≥ cn/2, 4n⁴e^{−11n} small, N ≤ n²) involve n only once r + ℓ ≤ κn
--   - encoding: G_n has N = nℓ variables and width at most w(ℓ+1)/2 → variables Fin n × Fin ℓ; 2 · width (lift F ℓ) ≤ w (ℓ + 1); reason: same instances
--   - reading: log |G_n| = O(ℓ + log n) → ∃ C′ (after k) with log encLength (lift F ℓ) ≤ C′ (ℓ + log n); reason: the O-constant may depend on the fixed data c, w and the size exponent k, as in the proof (|G_n| ≤ |F_n|·binom(ℓ, (ℓ+1)/2)^w)
--   - reading: the bound on lines, and on total size, is superpolynomial in |G_n| whenever (n/r)exp(−Cr/√ℓ) = ω(ℓ + log n) (37) → for every k′ there is M (after k) such that (n/r)exp(−Cr/√ℓ) ≥ M(ℓ + log n) implies encLength(G)^{k′} ≤ S and encLength(G)^{k′} ≤ T; reason: pins ω and 'superpolynomial' per n; along any sequence with ratio → ∞ it gives |G_n|^{k′} ≤ S, T eventually for every k′, which is the source's claim
--   - encoding: T, the number of monomial occurrences (Definition 2.7) → totalSize π = max 1 (monomial occurrences); reason: F has no empty clause (its complement 1 would be a degree-0 PC refutation), so every refutation of G contains a line with a monomial and the floor changes no instance
--   - encoding: log; S the number of lines → Real.log (natural logarithm); S = π.length; reason: the proof of (14)/(16) uses the natural logarithm (it compares S·e^{−ηt}); same instances
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Theorem 4.20, p.27 (proof p.27); Theorem 1.3, p.4; Definitions 1.2, 4.2, pp.4, 19–20

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_Supplement_ResPC

namespace AC02Frege.Supplement

open LiftSAParity

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower
Bounds*, manuscript (sha256 88d149fa…), Theorem 4.20, p.27 (majority extension with variable block
length). Fix `0 < c < 1` and a positive integer `w`. There are constants `ℓ₀, κ, c₁, C > 0`,
depending only on `c, w`, such that: if `F_n` is an unsatisfiable polynomial-size CNF on `n`
variables of width at most `w` with no PC refutation over `𝔽₂` of degree `D = ⌊cn⌋`, `ℓ ≥ ℓ₀` is
odd and `r ≥ 1` is an integer with `r + ℓ ≤ κn`, then for all sufficiently large `n` every `S`-line
syntactic `Res(PC_r)` refutation of `G_n = F_n ∘ Maj_ℓ` satisfies
`log S ≥ c₁ (n/r) exp(−C r/√ℓ)` (36). `G_n` has `N = nℓ` variables, width at most `w(ℓ+1)/2`, and
`log |G_n| = O(ℓ + log n)`; hence the bound on lines, and a fortiori on total size, is
superpolynomial in `|G_n|` whenever `(n/r) exp(−C r/√ℓ) = ω(ℓ + log n)` (37).

**Formalization Note** "Polynomial-size" is `encLength F ≤ n^k` for a fixed exponent `k`;
`O(ℓ + log n)` is an explicit constant `C′`, and the `ω` of (37) is pinned uniformly: for every
exponent `k′` there is `M` such that `(n/r) exp(−C r/√ℓ) ≥ M (ℓ + log n)` forces
`|G_n|^{k′} ≤ S` and `|G_n|^{k′} ≤ T` (equivalent to the sequence form of `ω`). `ℓ₀, κ, c₁, C` are
chosen before `k, k′` and do not depend on `n, ℓ, r`; `n₀, C′, M` may depend on `c, w, k, k′`. `|G|`
is the base `encLength`, `N = nℓ` is the variable type `Fin n × Fin ℓ`, and the width bound is
`2 · width(G_n) ≤ w(ℓ + 1)`. `log` is natural. -/
theorem theorem_4_20 :
    ∀ c : ℝ, 0 < c → c < 1 → ∀ w : ℕ, 1 ≤ w →
    ∃ ℓ₀ : ℕ, ∃ κ c₁ C : ℝ, 0 < ℓ₀ ∧ 0 < κ ∧ 0 < c₁ ∧ 0 < C ∧
    ∀ k k' : ℕ, ∃ n₀ : ℕ, ∃ C' M : ℝ, ∀ n : ℕ, n₀ ≤ n →
    ∀ F : CNF (Fin n), ¬ Satisfiable F → AC02Frege.encLength F ≤ n ^ k →
      (∀ J ∈ F, J.card ≤ w) → ¬ AC02Frege.PCDerivable F ⌊c * n⌋₊ 1 →
    ∀ ℓ : ℕ, Odd ℓ → ℓ₀ ≤ ℓ →
      2 * AC02Frege.width (AC02Frege.lift F ℓ) ≤ w * (ℓ + 1) ∧
      Real.log (AC02Frege.encLength (AC02Frege.lift F ℓ)) ≤ C' * (ℓ + Real.log n) ∧
      ∀ r : ℕ, 1 ≤ r → (r : ℝ) + ℓ ≤ κ * n →
      ∀ π : List (RLine (Fin n × Fin ℓ)), IsResRefutation (r : ℕ∞) (AC02Frege.lift F ℓ) π →
        c₁ * ((n : ℝ) / r) * Real.exp (-C * r / Real.sqrt ℓ) ≤ Real.log π.length ∧
        (M * (ℓ + Real.log n) ≤ (n : ℝ) / r * Real.exp (-C * r / Real.sqrt ℓ) →
          ((AC02Frege.encLength (AC02Frege.lift F ℓ) : ℝ) ^ k' ≤ π.length ∧
           (AC02Frege.encLength (AC02Frege.lift F ℓ) : ℝ) ^ k' ≤ totalSize π)) := by sorry

end AC02Frege.Supplement
