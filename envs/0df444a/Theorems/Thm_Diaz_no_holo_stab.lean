-- Prove2me | Theorems.Thm_Diaz_no_holo_stab
-- name    : Diaz.no_holo_stab
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:05:20.853706+00:00
-- url     : https://prove2.me/theorems/d80d18f7-c985-4e18-82a4-7ea131632d9f
-- title:
--   No holomorphic stabilizer: a Möbius map over $K$ fixing a transcendental point is the identity
-- statement:
--   **Source.** This is Carlo Perassi's mathematics, unpublished apart from this node. Published on his mission with his permission. No novelty is claimed for it here; the argument is elementary.
--
--   **Statement.** Let $K \subset \mathbb{C}$ be a subfield and $z$ transcendental over $K$. If $g(t) = (at+b)/(ct+d)$ has coefficients in $K$ and fixes $z$, then $c = b = 0$ and $a = d$ — that is, $g$ is the identity of $\mathrm{PGL}(2,K)$.
--
--   **What it is for.** The conjugation-degree framework studies a candidate through the action of $\Gamma = \mathrm{PGL}(2,\overline{\mathbb{Q}})$ and its extension by complex conjugation on $\mathbb{C}\setminus\overline{\mathbb{Q}}$. This lemma says the holomorphic part of that action is free on transcendental points, which is what makes the anti-holomorphic stabilizer of a point of conjugation degree one exactly $\{\mathrm{id}, R\}$ with $R$ the reflection in its canonical circle — and hence what makes the reflection $R_\rho(z) = \rho/\bar z$ the *unique* non-identity element of the stabilizer of a Diaz candidate. Note that non-degeneracy of $g$ is not needed: the conclusion already forces $ad - bc = a^2$.
--
--   **Proof.** Clearing the denominator, $az + b = z(cz+d)$, i.e. $cz^2 + (d-a)z + (-b) = 0$, a quadratic relation for $z$ with coefficients in $K$. Since $z$ is transcendental over $K$, the polynomial $cX^2 + (d-a)X - b \in K[X]$ is zero, so $c = 0$, $d = a$ and $b = 0$.

import Mathlib

open ComplexConjugate

theorem Diaz.no_holo_stab {K : Subfield ℂ} {z : ℂ} (hz : Transcendental K z)
    {a b c d : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K)
    (hden : c * z + d ≠ 0) (h : (a * z + b) / (c * z + d) = z) :
    c = 0 ∧ b = 0 ∧ a = d := by sorry
