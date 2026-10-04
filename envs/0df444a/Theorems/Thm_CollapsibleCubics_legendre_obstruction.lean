-- Prove2me | Theorems.Thm_CollapsibleCubics_legendre_obstruction
-- name    : CollapsibleCubics.legendre_obstruction
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-03T21:20:50.872188+00:00
-- url     : https://prove2.me/theorems/c00c32b3-372f-44dc-911c-46e852133251
-- title:
--   Legendre obstruction: primes dividing the norms of a collapsing must split completely
-- statement:
--   Let $m(x)=x^3+dx+e\in\mathbb{Z}[x]$ be irreducible over $\mathbb{Q}$ with discriminant $\Delta=-4d^3-27e^2$, let $\alpha\in\mathbb{C}$ be a root, and let
--   $$\prod_{i<n}(b_i\alpha-a_i)=c\in\mathbb{Q}$$
--   be a collapsing written in homogeneous form: $a_i,b_i\in\mathbb{Z}$ coprime, $b_i\neq0$ (so $b_i\alpha-a_i=b_i(\alpha-a_i/b_i)$; by the product criterion every collapsing has this form). Let $p$ be an odd prime with $p\nmid\Delta$ which divides one of the norms
--   $$F(a_j,b_j)=a_j^3+d\,a_j\,b_j^2+e\,b_j^3=\pm N_{K/\mathbb{Q}}(b_j\alpha-a_j).$$
--   Then $\Delta$ is a quadratic residue modulo $p$: $\left(\frac{\Delta}{p}\right)=1$. Equivalently (by the mission's Dedekind splitting criterion `CollapsibleCubics.splits_completely_iff_legendreSym`), $p$ splits completely in $K=\mathbb{Q}(\alpha)$, i.e. $m$ has three distinct roots modulo $p$.
--
--   **Why this matters.** Since $p\mid F(a_j,b_j)$ already forces $m$ to have a root mod $p$ (`exists_root_of_prime_dvd_form`), the statement excludes exactly the primes of splitting type $(1,2)$ — one linear and one irreducible quadratic factor mod $p$ — which by Chebotarev are **half of all primes** for an $S_3$ cubic. So the rationals $r=a/b$ usable in any collapsing form a sieved set: no value $F(a,b)$ may contain a prime with $\left(\frac{\Delta}{p}\right)=-1$. For a cyclic cubic ($\Delta$ a square) the condition is void, matching the known easy case. This is the arithmetic counterpart of the archimedean degree bound: together they explain why collapsings of $x^3+dx+1$ need large degree (the usable forms are rare and their unit exponents nearly cancel).
--
--   A proof sketch (via the splitting $K\otimes\mathbb{Q}_p\cong\mathbb{Q}_p\times L$, or via Dedekind–Kummer and ideal valuations) is given in the mission discussion.
--
--   **Formalization note.** Stated with the Legendre symbol `legendreSym p Δ` of Mathlib and `IsCoprime` for the pairs $(a_i,b_i)$; $n\ge1$ is implicit in the index $j$. A formal proof can go through Mathlib's Dedekind–Kummer theorem (`KummerDedekind`) and ideal valuations in $\mathcal{O}_K$, or through $p$-adic completions as in the sketch.
-- source:
--   New necessary condition for one-step collapsibility, derived in the Collapsible Cubics mission (S-unit analysis of the product criterion); companion to the Dedekind splitting milestone Q7 and the archimedean bound Q2.

import Mathlib
open Polynomial

namespace CollapsibleCubics
theorem legendre_obstruction (d e : ℤ)
    (hirr : Irreducible (X ^ 3 + C (d : ℚ) * X + C (e : ℚ) : ℚ[X]))
    (α : ℂ) (hα : α ^ 3 + (d : ℂ) * α + (e : ℂ) = 0)
    (n : ℕ) (a b : Fin n → ℤ) (hb : ∀ i, b i ≠ 0) (hab : ∀ i, IsCoprime (a i) (b i))
    (c : ℚ) (hprod : ∏ i, ((b i : ℂ) * α - (a i : ℂ)) = (c : ℂ))
    (p : ℕ) [Fact p.Prime] (hp : Odd p) (hpΔ : ¬ (p : ℤ) ∣ (-4 * d ^ 3 - 27 * e ^ 2))
    (j : Fin n) (hpF : (p : ℤ) ∣ a j ^ 3 + d * a j * b j ^ 2 + e * b j ^ 3) :
    legendreSym p (-4 * d ^ 3 - 27 * e ^ 2) = 1 := by sorry
end CollapsibleCubics
