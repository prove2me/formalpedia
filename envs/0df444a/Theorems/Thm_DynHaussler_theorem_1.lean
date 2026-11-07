-- Prove2me | Theorems.Thm_DynHaussler_theorem_1
-- name    : DynHaussler.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:37:52.714313+00:00
-- url     : https://prove2.me/theorems/ee1fc486-6b37-4c18-8326-f306be497232
-- title:
--   Theorem 1 — sharp global dynamic $\ell_p$ covering: $(c/\varepsilon)^{pd}\le\sup N^{\mathrm{dyn}}_p\le(C/\varepsilon)^{pd}$
-- statement:
--   There are universal constants $0<c\le1\le C$ such that the following four statements hold.
--
--   1. **Two-sided bound.** For every $1\le p<\infty$, every integer $d\ge0$ and every $0<\varepsilon<1/4$,
--   $$
--   \Bigl(\frac c\varepsilon\Bigr)^{pd}\le\sup_{X,\ T\ge1,\ \emptyset\neq F\subseteq[0,1]^X:\ \mathrm{sfat}_{\varepsilon/32}(F)\le d}N^{\mathrm{dyn}}_p(F,\varepsilon,T)\le\Bigl(\frac C\varepsilon\Bigr)^{pd}. \tag{2}
--   $$
--   2. **Per-class bound.** For every $1\le p<\infty$, every $T\ge1$ and every $0<\varepsilon<1/2$, each nonempty $F\subseteq[0,1]^X$ with $\mathrm{sfat}_{\varepsilon/32}(F)<\infty$ satisfies
--   $$
--   N^{\mathrm{dyn}}_p(F,\varepsilon,T)\le\Bigl(\frac{C}{\varepsilon^p}\Bigr)^{\mathrm{sfat}_{\varepsilon/32}(F)}. \tag{3}
--   $$
--   3. **Fixed hard class.** For each integer $d\ge1$ there is a countable binary class $H_d$ (on a countable domain) with $\mathrm{Ldim}(H_d)=\mathrm{sfat}_\gamma(H_d)=d$ for every $0<\gamma\le1$, fixed independently of $p$ and $\varepsilon$, such that for every $1\le p<\infty$ and $0<\varepsilon<1/4$ there are an integer $T_0=T_0(d,p,\varepsilon)\ge1$ and one infinite periodic instance sequence $\bar x$ with
--   $$
--   N^{\mathrm{dyn}}_p(H_d,\varepsilon,T)>\Bigl(\frac1{4\varepsilon}\Bigr)^{pd}\qquad(T\ge T_0), \tag{4}
--   $$
--   and for every $T\ge T_0$ the same strict bound holds for the number of arbitrary real vectors needed to cover $H_d$ on the prefix $\bar x_{1:T}$.
--   4. **Dimension zero.** If $\mathrm{sfat}_{\varepsilon/32}(F)=0$, one expert suffices: $N^{\mathrm{dyn}}_p(F,\varepsilon,T)=1$.
--
--   The constants are independent of $p,d,T$ and $\varepsilon$. This answers the dynamic analogue of Haussler's packing lemma asked for by Malliaris and Moran, and the global approximate covering question of Alon, Ben-Eliezer, Dagan, Moran, Naor and Yogev, with the sharp exponent $pd$.
--
--   **Formalization Note** The supremum in (2) is taken in the extended nonnegative reals over all nonempty domains $X$ in Lean's universe `Type` (every set has a copy there), all horizons $T\ge1$ and all nonempty $[0,1]$-valued classes with $\mathrm{sfat}_{\varepsilon/32}(F)\le d$. In clause 3 the domain and the class come before $p,\varepsilon$, and $T_0$ and $\bar x:\mathbb N\to X$ (0-based) come after $(p,\varepsilon)$ and before $T$. Domains are nonempty, as the paper assumes throughout.
--
--   Differences from the source:
--   - encoding: the supremum over all (nonempty) sets X → the supremum in ℝ≥0∞ over all nonempty X : Type; reason: every set has a copy in Type, and N^dyn is invariant under relabelling the domain
--   - generalization: a countable binary class H_d → a countable binary class on a countable domain X; reason: the domain is also asserted countable (Theorem 6); this only adds a conclusion
--   - generalization: one periodic sequence witnesses the bound on every prefix, even when the covering experts are allowed real-valued predictions → on every prefix of length T ≥ T_0, any n vectors in ℝ^T that cover H_d on the prefix have n > (1/(4ε))^{pd}; reason: read through Theorem 6 (covering only on the prefix, by arbitrary vectors); every real-valued causal expert gives one such vector, so this implies the source's claim
--   - generalization: "if sfat_{ε/32}(F) = 0, one expert suffices" in the theorem's ranges of ε → N^dyn_p(F, ε, T) = 1 for every ε > 0; reason: the midpoint expert has pointwise error ≤ ε/64; the source's ranges are instances
--   - encoding: one expert suffices → N^dyn_p(F, ε, T) = 1; reason: N^dyn_p ≥ 1 for nonempty F, nonempty X and T ≥ 1
--   - encoding: the periodic sequence (x̄_t)_{t≥1} → xbar : ℕ → X (0-based), periodic: ∃ L > 0, ∀ t, xbar (t + L) = xbar t; reason: index shift only
--   - encoding: N^dyn_p ∈ ℕ ∪ {∞} compared with real numbers → dynCoverNum in ℕ∞, compared through ℕ∞ → ℝ≥0∞ with ENNReal.ofReal of the real bound; reason: same order on the nonnegative extended reals
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Theorem 1, Eqs. (2)–(4), p.2 (PDF p.4); via Theorems 5, 6 and (22)–(24), pp.14–15 (PDF pp.16–17)

import Mathlib
import Definitions.Def_DynHaussler_dynCoverNum
import Definitions.Def_DynHaussler_ldim
import Definitions.Def_NondualOpt_sfat

set_option autoImplicit false

namespace DynHaussler

universe u

/-- **Theorem 1 (Sharp global dynamic `ℓ_p` covering).** There are universal constants
`0 < c ≤ 1 ≤ C` such that, for every `1 ≤ p < ∞`, every integer `d ≥ 0`, and every `0 < ε < 1/4`,
`(c/ε)^{pd} ≤ sup_{X, T ≥ 1, ∅ ≠ F ⊆ [0,1]^X : sfat_{ε/32}(F) ≤ d} N^dyn_p(F, ε, T) ≤ (C/ε)^{pd}`
(Eq. (2)). More precisely, for every `1 ≤ p < ∞`, every `T ≥ 1`, and every `0 < ε < 1/2`, each
nonempty class `F ⊆ [0,1]^X` with `sfat_{ε/32}(F) < ∞` satisfies
`N^dyn_p(F, ε, T) ≤ (C/ε^p)^{sfat_{ε/32}(F)}` (Eq. (3)). Moreover, for each integer `d ≥ 1`, there is a
countable binary class `H_d` with `Ldim(H_d) = sfat_γ(H_d) = d` for every `0 < γ ≤ 1`, fixed
independently of `p` and `ε`, such that, for every `1 ≤ p < ∞` and `0 < ε < 1/4`, there is an integer
`T_0 = T_0(d, p, ε) ≥ 1` for which `N^dyn_p(H_d, ε, T) > (1/(4ε))^{pd}` (`T ≥ T_0`) (Eq. (4)). For each
`p, ε`, one fixed infinite periodic instance sequence witnesses this lower bound on every prefix of
length `T ≥ T_0`, even when the covering experts are allowed real-valued predictions. The constants
are independent of `p, d, T`, and `ε`. If `sfat_{ε/32}(F) = 0`, one expert suffices.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Theorem 1, Eqs. (2)–(4), p.2 (PDF p.4); proved via Theorems 5, 6 and (22)–(24),
pp.14–15 (PDF pp.16–17).

The statement is the conjunction of four clauses, after `∃ c C`:
(A) the two-sided bound (2) on the supremum; (B) the per-class bound (3); (C) the fixed class
`H_d` with the lower bound (4) and the fixed periodic sequence; (D) one expert when
`sfat_{ε/32}(F) = 0`.

**Formalization Note** `c, C` are chosen before every other parameter. The supremum in (A) is taken
in `ℝ≥0∞` over all nonempty domains `X : Type` (every set has a copy in `Type`), all horizons
`T ≥ 1`, and all nonempty `F ⊆ [0,1]^X` with `sfat_{ε/32}(F) ≤ d`; `N^dyn_p` lies in `ℕ∞` (`⊤` if no
finite cover exists) and is compared through `ℕ∞ → ℝ≥0∞`. Real powers are `Real.rpow`. In (C) the
domain and the class are existential and chosen before `p, ε`; `T_0` and the periodic sequence
`x̄ : ℕ → X` (0-based, prefix `(x̄_0, …, x̄_{T−1})`) are chosen after `(p, ε)` and before `T`; "even when
the covering experts are allowed real-valued predictions" is read as in Theorem 6: covering is
required only on the prefix, by arbitrary vectors in `ℝ^T`. (D) is stated for every `ε > 0`, as
`N^dyn_p = 1`. Domains are nonempty (the paper's standing assumption, Section 3). -/
theorem theorem_1 :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
    -- (A) Eq. (2)
    (∀ p : ℝ, 1 ≤ p → ∀ d : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
      ENNReal.ofReal ((c / ε) ^ (p * d)) ≤
        (⨆ (X : Type) (_ : Nonempty X) (T : ℕ) (_ : 1 ≤ T) (F : Set (X → ℝ)) (_ : F.Nonempty)
            (_ : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (_ : NondualOpt.sfat F (ε / 32) ≤ d),
            ((dynCoverNum p ε F T : ℕ∞) : ENNReal)) ∧
      (⨆ (X : Type) (_ : Nonempty X) (T : ℕ) (_ : 1 ≤ T) (F : Set (X → ℝ)) (_ : F.Nonempty)
            (_ : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (_ : NondualOpt.sfat F (ε / 32) ≤ d),
            ((dynCoverNum p ε F T : ℕ∞) : ENNReal)) ≤
        ENNReal.ofReal ((C / ε) ^ (p * d))) ∧
    -- (B) Eq. (3)
    (∀ p : ℝ, 1 ≤ p → ∀ T : ℕ, 1 ≤ T → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∀ (X : Type u) [Nonempty X] (F : Set (X → ℝ)), F.Nonempty →
        (∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
        ∀ s : ℕ, NondualOpt.sfat F (ε / 32) = s →
          ((dynCoverNum p ε F T : ℕ∞) : ENNReal) ≤ ENNReal.ofReal ((C / ε ^ p) ^ s)) ∧
    -- (C) Eq. (4) and the fixed periodic sequence
    (∀ d : ℕ, 1 ≤ d →
      ∃ (X : Type) (_ : Countable X) (H : Set (X → ℝ)), H.Countable ∧
        (∀ h ∈ H, ∀ x, h x = 0 ∨ h x = 1) ∧ ldim H = d ∧
        (∀ γ : ℝ, 0 < γ → γ ≤ 1 → NondualOpt.sfat H γ = d) ∧
        ∀ p : ℝ, 1 ≤ p → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
          ∃ T₀ : ℕ, 1 ≤ T₀ ∧ ∃ xbar : ℕ → X, (∃ L : ℕ, 0 < L ∧ ∀ t, xbar (t + L) = xbar t) ∧
            ∀ T : ℕ, T₀ ≤ T →
              ENNReal.ofReal ((1 / (4 * ε)) ^ (p * d)) < ((dynCoverNum p ε H T : ℕ∞) : ENNReal) ∧
              ∀ (n : ℕ) (W : Fin n → Fin T → ℝ),
                (∀ h ∈ H, ∃ i : Fin n, rho p (W i) (fun t => h (xbar t)) ≤ ε) →
                (1 / (4 * ε)) ^ (p * d) < n) ∧
    -- (D) one expert when sfat_{ε/32}(F) = 0
    (∀ p : ℝ, 1 ≤ p → ∀ T : ℕ, 1 ≤ T → ∀ ε : ℝ, 0 < ε →
      ∀ (X : Type u) [Nonempty X] (F : Set (X → ℝ)), F.Nonempty →
        (∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
        NondualOpt.sfat F (ε / 32) = 0 → dynCoverNum p ε F T = 1) := by sorry

end DynHaussler
