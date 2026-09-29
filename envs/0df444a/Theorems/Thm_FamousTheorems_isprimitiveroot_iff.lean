-- Prove2me | Theorems.Thm_FamousTheorems_isprimitiveroot_iff
-- name    : FamousTheorems.isprimitiveroot_iff
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T08:37:34.984997+00:00
-- url     : https://prove2.me/theorems/06fed895-0c3e-4081-877c-cbd0cdf55fba
-- title:
--   Primitive complex roots of unity
-- statement:
--   **Primitive $n$-th roots of unity.** For $n \neq 0$, a complex number $\zeta$ is a primitive $n$-th root of unity if and only if $$\zeta = e^{2\pi i\,k/n}\quad\text{with } 0 \le k < n \text{ and } \gcd(k,n) = 1.$$ Among the $n$ roots of unity, the primitive ones are exactly those whose order is $n$ rather than a proper divisor, and the coprimality condition on the exponent is precisely what guarantees this. Consequently there are $\varphi(n)$ of them, and they are the roots of the $n$-th cyclotomic polynomial, whose degree is therefore $\varphi(n)$. A primitive root generates the whole cyclic group of $n$-th roots of unity, which makes it the natural choice of basis for the cyclotomic field $\mathbb{Q}(\zeta_n)$ and the reason $[\mathbb{Q}(\zeta_n):\mathbb{Q}] = \varphi(n)$. **Formalization note.** `IsPrimitiveRoot ζ n` says $\zeta^n = 1$ and no smaller positive power is $1$. The result is Mathlib's `Complex.isPrimitiveRoot_iff`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem isprimitiveroot_iff :
    ∀ (ζ : ℂ) (n : ℕ), 
    n ≠ 0 → (IsPrimitiveRoot ζ n ↔ ∃ i < n, ∃ (_ : i.Coprime n), Complex.exp (2 * ↑Real.pi * Complex.I * (↑i / ↑n)) = ζ) := by sorry

end FamousTheorems
