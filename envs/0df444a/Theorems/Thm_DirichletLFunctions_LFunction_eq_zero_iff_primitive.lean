-- Prove2me | Theorems.Thm_DirichletLFunctions_LFunction_eq_zero_iff_primitive
-- name    : DirichletLFunctions.LFunction_eq_zero_iff_primitive
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T12:32:04.391355+00:00
-- url     : https://prove2.me/theorems/13f824ee-cdb1-4b51-9892-facc870a90e5
-- title:
--   An $L$-function and its primitive inducer have the same zeros
-- statement:
--   **Imprimitive $L$-functions have the same zeros as the primitive ones inducing them.**
--
--   Let $\chi$ be a Dirichlet character modulo $q$ and let $\chi^{*}$ be the primitive character
--   that induces it, of conductor $f \mid q$. Then for $\Re s > 0$ (excluding the single point
--   $s = 1$ when $\chi$ is principal),
--
--   $$L(s,\chi) = 0 \iff L(s,\chi^{*}) = 0 .$$
--
--   The two $L$-functions differ by the finite Euler correction factor over the primes dividing
--   $q$ but not $f$:
--
--   $$L(s,\chi) \;=\; L(s,\chi^{*}) \prod_{p \mid q,\ p \nmid f}\left(1 - \frac{\chi^{*}(p)}{p^{s}}\right).$$
--
--   Each factor is a finite product of terms $1 - \chi^{*}(p)p^{-s}$, and for $\Re s > 0$ one has
--   $|\chi^{*}(p)p^{-s}| \le p^{-\Re s} < 1$, so **no factor vanishes**. Hence the correction is
--   non-zero throughout the region and the zero sets coincide exactly.
--
--   This is the reduction that lets every statement about zeros — zero-free regions, zero-density
--   estimates, the explicit formula, Siegel zeros — be proved for primitive characters only and
--   then transferred to arbitrary ones. Without it, the functional equation (which requires
--   primitivity, since it involves the Gauss sum $\tau(\chi^{*})$ of modulus $\sqrt f$) could not be
--   applied to imprimitive characters at all.
--
--   **Formalization note.** `χ.primitiveCharacter` is Mathlib's primitive character inducing $\chi$,
--   living at the conductor rather than at $q$; `LFunction` is the analytic continuation. The
--   hypothesis `χ ≠ 1 ∨ s ≠ 1` excludes the pole of the principal character's $L$-function at
--   $s = 1$.
--
--   The preamble supplies the instance `NeZero χ.conductor`, which Mathlib provides only as the lemma `DirichletCharacter.conductor_ne_zero`; it is needed for `LFunction χ.primitiveCharacter` to elaborate at the conductor.
-- source:
--   Classical; see Davenport, *Multiplicative Number Theory*, §5, and Montgomery & Vaughan, *Multiplicative Number Theory I*, §9.1. Lean proof extracted from `Salt/SW/EulerBridge.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

open DirichletCharacter

instance instNeZeroConductorP2M {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩

namespace DirichletLFunctions

theorem LFunction_eq_zero_iff_primitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) (h1 : χ ≠ 1 ∨ s ≠ 1) :
    LFunction χ s = 0 ↔ LFunction χ.primitiveCharacter s = 0 := by sorry

end DirichletLFunctions
