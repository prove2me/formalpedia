-- Prove2me | Theorems.Thm_ApproxGKR_lemma_C_2
-- name    : ApproxGKR.lemma_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:57.169147+00:00
-- url     : https://prove2.me/theorems/70255457-3e85-4c5a-bd6f-9df82309d958
-- title:
--   Lemma C.2 — anti-concentration of a polynomial on $\Omega_N$
-- statement:
--   Let $f\in\mathbb C[X]$ be nonzero of degree at most $D\ge1$, and let $M(f)=\max_{|z|=1}|f(z)|$. Let $N\ge1$ and $h\ge1$.
--   1. For $0<\alpha<1$,
--   $$\Pr_{r\leftarrow\Omega_N}\big[|f(r)|\le\alpha M(f)\big]\le D\big(\alpha^{1/D}+N^{-1}\big).\tag{C.10}$$
--   2. $M(f)\ge\big|\sum_{a\in\Omega_h}f(a)\big|/h$.
--   3. For fixed $e_a,e_b\in\mathbb C$ with $e=\max\{|e_a|,|e_b|\}>0$ and $0<\beta<1$,
--   $$\Pr_{\lambda\leftarrow\Omega_N}\big[|e_a+\lambda e_b|\le\beta e\big]\le\beta+N^{-1}.\tag{C.11}$$
--   4. There is a set $Z\subseteq\Omega_N$ of at most $\deg f$ points, containing every zero of $f$ in $\Omega_N$, such that for every $0<s<1/D$
--   $$\frac1N\sum_{r\in\Omega_N\setminus Z}\Big(\frac{M(f)}{|f(r)|}\Big)^s\le\frac1{1-Ds}.\tag{C.12}$$
--
--   The lemma replaces the Schwartz–Zippel zero count: a nonzero value can still be too small for an approximate check to detect, and (C.10) bounds how often that happens.
--
--   Differences from the source:
--   - generalization: N and h powers of two (the protocol's) → any N ≥ 1 and h ≥ 1; reason: the arc argument does not use powers of two
--   - encoding: M(f) = max_{|z|=1}|f(z)| → the supremum of |f| on the unit circle; reason: the maximum is attained on the compact circle, so they agree
--   - encoding: probabilities over r ← Ω_N; Z ⊆ Ω_N → counts over the indices Fin N divided by N; Z a set of indices; reason: indices and roots of Ω_N correspond one to one
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.3, Lemma C.2, p.36

import Mathlib
import Definitions.Def_ApproxGKR_root

namespace ApproxGKR

open Classical in
/-- **Lemma C.2 (Anti-concentration)** (p.36).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.3, Lemma C.2, p.36: "Let `f ∈ C[X]` be nonzero of degree at most `D ≥ 1`,
and let `M(f) = max_{|z|=1} |f(z)|`. For `0 < α < 1`,
`Pr_{r←ΩN}[|f(r)| ≤ αM(f)] ≤ D(α^{1/D} + N^{−1})`. (C.10) Moreover, `M(f) ≥ |Σ_{a∈H} f(a)|/h`.
For fixed `ea, eb ∈ C` and `e = max{|ea|, |eb|} > 0`,
`Pr_{λ←ΩN}[|ea + λeb| ≤ βe] ≤ β + N^{−1}` (`0 < β < 1`). (C.11) There is a set `Z ⊆ ΩN` of at most
`deg f` points, containing every zero of `f` in `ΩN`, such that for every `0 < s < 1/D`,
`(1/N) Σ_{r∈ΩN∖Z} (M(f)/|f(r)|)^s ≤ 1/(1 − Ds)`. (C.12)"

All four clauses, for every `N ≥ 1` and every `h ≥ 1`.

**Formalization Note** `M(f)` is the supremum of `|f|` on the unit circle (a maximum, since the
circle is compact and the set is nonempty and bounded). `Ω_N` is indexed by `Fin N`; a
probability over `r ← Ω_N` is a count divided by `N`. `Z` is a set of indices, chosen once for all
`s` (quantifier order as printed). `α^{1/D}` is the real power. -/
theorem lemma_C_2 (f : Polynomial ℂ) (D N h : ℕ) (hf : f ≠ 0) (hdeg : f.natDegree ≤ D)
    (hD : 1 ≤ D) (hN : 1 ≤ N) (hh : 1 ≤ h) :
    let M : ℝ := sSup ((fun z : ℂ => ‖f.eval z‖) '' {z : ℂ | ‖z‖ = 1})
    (∀ α : ℝ, 0 < α → α < 1 →
      ((Finset.univ.filter (fun r : Fin N => ‖f.eval (root N r.val)‖ ≤ α * M)).card : ℝ) / N ≤
        D * (α ^ ((1 : ℝ) / D) + 1 / N)) ∧
    ‖∑ a : Fin h, f.eval (root h a.val)‖ / h ≤ M ∧
    (∀ (ea eb : ℂ) (β : ℝ), 0 < max ‖ea‖ ‖eb‖ → 0 < β → β < 1 →
      ((Finset.univ.filter (fun l : Fin N =>
          ‖ea + root N l.val * eb‖ ≤ β * max ‖ea‖ ‖eb‖)).card : ℝ) / N ≤ β + 1 / N) ∧
    (∃ Z : Finset (Fin N), Z.card ≤ f.natDegree ∧
      (∀ r : Fin N, f.eval (root N r.val) = 0 → r ∈ Z) ∧
      ∀ s : ℝ, 0 < s → s < 1 / D →
        (1 / (N : ℝ)) * ∑ r ∈ Finset.univ \ Z, (M / ‖f.eval (root N r.val)‖) ^ s ≤
          1 / (1 - D * s)) := by sorry

end ApproxGKR
