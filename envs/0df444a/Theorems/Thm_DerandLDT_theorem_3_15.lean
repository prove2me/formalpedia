-- Prove2me | Theorems.Thm_DerandLDT_theorem_3_15
-- name    : DerandLDT.theorem_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:31.81409+00:00
-- url     : https://prove2.me/theorems/727f19b4-1d69-4d69-b4a8-e5d84e074f4d
-- title:
--   Theorem 3.15 — Newton iteration: $\Phi_k$ is the unique degree-$\le k$ root of $P$ modulo $Y^{k+1}$
-- statement:
--   Let $K$ be a field, $P(Y, Z) \in K[Y, Z]$ and $a \in K$ with $P(0, a) = 0$ and $\alpha = \partial_Z(P)(0, a) \neq 0$. Let $\Phi_0 = a$ and $\Phi_k = (\Phi_{k-1} - P(Y, \Phi_{k-1})/\alpha) \bmod Y^{k+1}$ for $k \ge 1$. Then for every $k \ge 1$, $\Phi_k(Y)$ is the unique polynomial $\Psi \in K[Y]$ with
--   $$
--   P(Y, \Psi(Y)) \equiv 0 \pmod{Y^{k+1}}, \qquad \Psi(Y) \equiv a \pmod{Y}, \qquad \deg \Psi \le k .
--   $$
--   In Lemma 4.1 this is applied over $K = \mathbb F(X)$ to lift the root $h(X)$ on the anchor line to a power-series root, and its uniqueness identifies the lift with the roots $g_a$ on the parallel lines.
--
--   **Formalization Note** $P$ is a polynomial in $Z$ with coefficients in $K[Y]$, and $\Phi_k$ is `DerandLDT.newtonApprox P a k`.
--
--   Differences from the source:
--   - generalization: P ∈ F[Y, Z] for a subfield F of K → P ∈ K[Y, Z]; reason: F[Y, Z] ⊆ K[Y, Z], so the paper's case is an instance
--   - reading: "Φ(Y) ≡ a mod Y" → Φ_k(Y) ≡ a mod Y; reason: typo: the conditions are about Φ_k
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Theorem 3.15, p.14

import Definitions.Def_DerandLDT_newtonApprox

set_option autoImplicit false

universe u

namespace DerandLDT

open Polynomial

/-- **Theorem 3.15** (Newton iteration). Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point
low-degree test*, STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Theorem 3.15, p.14: *Let `F` be any field, `K`
an extension of `F`, `P(Y, Z) ∈ F[Y, Z]`, and `a ∈ K` with `P(0, a) = 0` and
`∂_Z(P)(0, a) ≠ 0`. Let `Φ₀ := a` and `Φ_k := (Φ_{k-1} − P(Y, Φ_{k-1})/∂_Z(P)(0, a)) mod Y^{k+1}`.
Then for every `k ≥ 1`, `Φ_k(Y)` is the unique polynomial with `P(Y, Φ_k(Y)) ≡ 0 mod Y^{k+1}`,
`Φ_k(Y) ≡ a mod Y` and `deg Φ_k ≤ k`.*

**Formalization Note.** `P : K[X][X]` is a polynomial in `Z` (outer) with coefficients in
`K[Y]` (inner); `Φ_k` is `newtonApprox P a k`. The statement is made for every `P` with
coefficients in `K`, which contains the paper's `P ∈ F[Y, Z] ⊆ K[Y, Z]`. The printed
"`Φ(Y) ≡ a mod Y`" is read as `Φ_k(Y) ≡ a mod Y`. -/
theorem theorem_3_15 (K : Type u) [Field K] (P : K[X][X]) (a : K)
    (h0 : (P.eval (C a)).eval 0 = 0) (h1 : ((derivative P).eval (C a)).eval 0 ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) :
    ((X : K[X]) ^ (k + 1) ∣ P.eval (newtonApprox P a k) ∧
        (X : K[X]) ∣ newtonApprox P a k - C a ∧ (newtonApprox P a k).natDegree ≤ k) ∧
      ∀ Ψ : K[X], (X : K[X]) ^ (k + 1) ∣ P.eval Ψ → (X : K[X]) ∣ Ψ - C a →
        Ψ.natDegree ≤ k → Ψ = newtonApprox P a k := by sorry

end DerandLDT
