-- Prove2me | Theorems.Thm_CKKSPrecision_FourierUnits_lemma_4_1
-- name    : CKKSPrecision.FourierUnits.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:44:56.963218+00:00
-- url     : https://prove2.me/theorems/54e715bb-1131-41a7-85b4-d7021b43d6da
-- title:
--   Lemma 4.1 — conjugate logarithms span and nonzero Fourier modes
-- statement:
--   Let $r\ge2$ be a power of two, with $u_0$, $\tau$, the cyclic embedding order and $\ell_j=\log_2|\sigma_j(u_0)|$ as above. With the unnormalized negative-exponent forward Fourier transform,
--   $$
--   \operatorname{span}_{\mathbb R}\{\operatorname{Log}(\tau^k(u_0)):0\le k<r\}=H,
--   \qquad \widehat\ell_0=0,
--   \qquad \widehat\ell_k\ne0\quad(1\le k<r).
--   $$
--   These are all clauses of the lemma. The last clause makes every nonzero-frequency division in the construction meaningful for every zero-sum real target.
--
--   Differences from the source:
--   - encoding: $K=\mathbb Q(\zeta)$ with the specified primitive complex root → Mathlib splitting field with the distinguished root sent to $\exp(2\pi i/m)$ by a fixed embedding; reason: an isomorphic model of the same field and root, with no additional hypothesis
--   - encoding: cyclic indices $0\le j,k<r$ → `Fin r` coordinates, with zero frequency written as the element of value zero; reason: this enumerates exactly the same embedding order and Fourier modes
--   - encoding: a power-of-two integer dimension $r\ge2$ and real vectors in $\mathbb R^r$ with the infinity norm → a positive natural dimension with $r\ge2$, $r=2^q$ for some natural $q$, and functions `Fin r` to the reals with their supremum norm; reason: these encode exactly the same dimensions, coordinates and norm, without restricting target values
-- source:
--   Zhaoyang Liang, Runkun Liu, Jingwei Fang, Dan Ding, A New Approach to Reducing Modulus Requirements in Homomorphic Computation: Precision Allocation in CKKS, STOC 2027 submission #148 (October 2026), p. 8, Lemma 4.1; Section 4.2 standing assumptions on p. 7 (PDF pp. 9–10)

import Definitions.Def_CKKSPrecision_FourierUnits_fourier_construction

set_option autoImplicit false

namespace CKKSPrecision.FourierUnits

theorem lemma_4_1 (r : ℕ+) (hr : 2 ≤ (r : ℕ))
    (hp : ∃ q : ℕ, (r : ℕ) = 2 ^ q) :
    Submodule.span ℝ (Set.range (conjugateLogs r)) = H (Fin (r : ℕ)) ∧
      fourier r (fun j => (ell r j : ℂ)) ⟨0, r.pos⟩ = 0 ∧
      ∀ k : Fin (r : ℕ), 0 < k.val →
        fourier r (fun j => (ell r j : ℂ)) k ≠ 0 := by sorry

end CKKSPrecision.FourierUnits
