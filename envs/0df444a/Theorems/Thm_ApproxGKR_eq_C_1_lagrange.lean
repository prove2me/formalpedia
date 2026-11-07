-- Prove2me | Theorems.Thm_ApproxGKR_eq_C_1_lagrange
-- name    : ApproxGKR.eq_C_1_lagrange
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:41.101791+00:00
-- url     : https://prove2.me/theorems/6d8744f5-9988-4eac-a907-31ef39e88402
-- title:
--   (C.1) — Lagrange basis, interpolation at labels, degree bound and uniqueness
-- statement:
--   Let $h\ge1$, $H=\Omega_h$, $m\ge0$ and let $f$ be any complex function on the labels $H^m$, with extension $\widetilde f=\sum_g f(g)\chi_g$. Then:
--   1. $L_a(a')=1$ if $a=a'$ and $0$ for the other $a'\in H$;
--   2. $\chi_g(g')=1$ if $g=g'$ and $0$ for every other label $g'$;
--   3. $\widetilde f(g)=f(g)$ at every label $g\in H^m$;
--   4. $\widetilde f$ has degree at most $h-1$ in each variable;
--   5. every polynomial of degree at most $h-1$ in each variable that agrees with $f$ on $H^m$ equals $\widetilde f$.
--
--   These facts make $\widetilde V_i$ the unique low-degree encoding of the gate values of layer $i$.
--
--   Differences from the source:
--   - generalization: h a power of two ≥ 2 → any h ≥ 1; reason: the five facts hold for every h ≥ 1 and specialize to the page's h
--   - generalization: the gate values V_i → any function f on the labels H^m; reason: specializes to f = V_i
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.1, eq. (C.1), p.30

import Mathlib
import Definitions.Def_ApproxGKR_lagrangeBasis

namespace ApproxGKR

/-- **Equation (C.1) and its interpolation facts** (p.30).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.1, p.30: "The geometric sum makes `La` a Lagrange basis polynomial, wherin it
equals one at `a` and zero at the other points of `H`. The product `χg` equals one at `g` and zero
at every other label, giving `Ṽi(g) = Vi(g)`." "The extension has degree at most `h − 1` in each
coordinate and is unique with these degree bounds".

For every function `f` on the labels `H^m` (the page's `f = Vᵢ`):
1. `L_a(a') = [a = a']` on `H`;
2. `χ_g(g') = [g = g']` on `H^m`;
3. `Ṽ(g) = f(g)` at every label;
4. `Ṽ` has degree at most `h − 1` in each variable;
5. `Ṽ` is the only polynomial with these degree bounds that agrees with `f` on `H^m`.

**Formalization Note** Stated for every `h ≥ 1` (the page fixes a power of two `h ≥ 2`). -/
theorem eq_C_1_lagrange (h m : ℕ) (hh : 1 ≤ h) (f : (Fin m → Fin h) → ℂ) :
    (∀ a a' : Fin h, (lagrangeBasis h a).eval (root h a'.val) = if a = a' then 1 else 0) ∧
    (∀ g g' : Fin m → Fin h,
      MvPolynomial.eval (labelPoint g') (chi g) = if g = g' then 1 else 0) ∧
    (∀ g : Fin m → Fin h, MvPolynomial.eval (labelPoint g) (extension f) = f g) ∧
    (∀ j : Fin m, (extension f).degreeOf j ≤ h - 1) ∧
    (∀ P : MvPolynomial (Fin m) ℂ, (∀ j, P.degreeOf j ≤ h - 1) →
      (∀ g : Fin m → Fin h, MvPolynomial.eval (labelPoint g) P = f g) → P = extension f) := by sorry

end ApproxGKR
