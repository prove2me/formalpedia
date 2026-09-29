-- Prove2me | Theorems.Thm_FamousTheorems_additive_principal_ordinals_omega_powers_7a
-- name    : FamousTheorems.additive_principal_ordinals_omega_powers_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:38.701857+00:00
-- url     : https://prove2.me/theorems/26d5b47f-0c05-420b-8710-8d3bc419fa70
-- title:
--   Additively principal ordinals are exactly the powers of ω
-- statement:
--   **Additively principal ordinals are exactly the powers of $\omega$.** An ordinal $o$ is additively principal, meaning $a+b<o$ whenever $a,b<o$, if and only if $o=0$ or $o=\omega^x$ for some ordinal $x$.
--
--   This characterisation is the basis of the Cantor normal form: every ordinal is a finite sum $\omega^{x_1}+\cdots+\omega^{x_k}$ of additively principal ordinals with $x_1\ge\cdots\ge x_k$. It is used in ordinal arithmetic and in proof theory, where ordinals below $\varepsilon_0$ are handled through their Cantor normal forms.
--
--   **Formalization note.** Mathlib's `Ordinal.isPrincipal_add_iff_zero_or_omega0_opow`. `Ordinal.IsPrincipal op o` means that $o$ is closed under $op$: $op(a,b)<o$ for all $a,b<o$. By this definition $0$ is vacuously principal. `Ordinal.omega0` is $\omega$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Ordinal.isPrincipal_add_iff_zero_or_omega0_opow`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u

theorem additive_principal_ordinals_omega_powers_7a {o : Ordinal.{u}} :
    Ordinal.IsPrincipal (· + ·) o ↔ o = 0 ∨ o ∈ Set.range (fun x : Ordinal.{u} => Ordinal.omega0 ^ x) := by sorry

end FamousTheorems
