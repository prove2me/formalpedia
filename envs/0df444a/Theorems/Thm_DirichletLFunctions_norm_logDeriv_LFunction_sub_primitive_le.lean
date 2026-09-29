-- Prove2me | Theorems.Thm_DirichletLFunctions_norm_logDeriv_LFunction_sub_primitive_le
-- name    : DirichletLFunctions.norm_logDeriv_LFunction_sub_primitive_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T16:29:02.03402+00:00
-- url     : https://prove2.me/theorems/48f32788-af59-4aad-b66e-4cc2b6967c8a
-- title:
--   The log-derivative gap between an $L$-function and its primitive inducer
-- statement:
--   **The logarithmic derivatives of $L(s,\chi)$ and $L(s,\chi^{*})$ differ by at most $\log q$.**
--
--   Let $\chi$ be a Dirichlet character mod $q$ and $\chi^{*}$ the primitive character inducing it.
--   For $\Re s \ge 1$ (with the pole of the principal character excluded, and assuming
--   $L(s,\chi^{*}) \ne 0$),
--
--   $$\left\| \frac{L'}{L}(s,\chi) - \frac{L'}{L}(s,\chi^{*}) \right\| \;\le\; \log q .$$
--
--   The two $L$-functions differ by the finite Euler product over primes $p \mid q$ with
--   $p \nmid f$, so their logarithmic derivatives differ by
--   $\sum_{p \mid q} \tfrac{\chi^{*}(p)\log p}{p^{s} - \chi^{*}(p)}$. On $\Re s \ge 1$ each term is
--   bounded by $\tfrac{\log p}{p - 1}$, and summing over the distinct primes dividing $q$ gives at
--   most $\sum_{p\mid q}\log p = \log\!\big(\mathrm{rad}(q)\big) \le \log q$.
--
--   The bound is exactly the error one pays for replacing an imprimitive character by the primitive
--   one inducing it, and it is **uniform**: $\log q$ is the natural scale in every explicit-formula
--   or zero-free-region estimate, so a discrepancy of that size is harmless. This is what lets the
--   analytic theory be developed for primitive characters and transported to arbitrary moduli.
--
--   **Formalization note.** `logDeriv f = deriv f / f`; the hypothesis $L(s,\chi^{*}) \ne 0$ is what
--   makes both logarithmic derivatives defined at $s$.
--
--   The preamble supplies the instance `NeZero χ.conductor`, which Mathlib provides only as the lemma `DirichletCharacter.conductor_ne_zero`.
-- source:
--   Classical; see Montgomery & Vaughan, *Multiplicative Number Theory I*, §9.1 and §11.3. Lean proof extracted from `Salt/SW/EulerBridge.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

open DirichletCharacter

instance instNeZeroConductorP2M {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩

namespace DirichletLFunctions

theorem norm_logDeriv_LFunction_sub_primitive_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 ≤ s.re) (hL₁ : LFunction χ.primitiveCharacter s ≠ 0)
    (h1 : χ ≠ 1 ∨ s ≠ 1) :
    ‖logDeriv (LFunction χ) s - logDeriv (LFunction χ.primitiveCharacter) s‖ ≤ Real.log q := by sorry

end DirichletLFunctions
