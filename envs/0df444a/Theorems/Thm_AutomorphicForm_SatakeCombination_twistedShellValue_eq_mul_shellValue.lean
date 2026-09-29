-- Prove2me | Theorems.Thm_AutomorphicForm_SatakeCombination_twistedShellValue_eq_mul_shellValue
-- name    : AutomorphicForm.SatakeCombination.twistedShellValue_eq_mul_shellValue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/91970303-db27-5980-a7c0-d26157c1df3d
-- title:
--   Twisted shell value equals ℓ times the base-change shell value
-- statement:
--   Fix natural numbers $q,\ell\ge 1$ and two double sequences of natural numbers $W_q,W_Q:\mathbb N\times\mathbb N\to\mathbb N$ subject to the walk recursions $W_q(0,0)=1$, $W_q(0,s+1)=0$, $W_q(n+1,0)=(q+1)W_q(n,1)$, $W_q(n+1,s+1)=W_q(n,s)+qW_q(n,s+2)$, and the same four identities for $W_Q$ with $q$ replaced by $q^{\ell}$. Fix $k,j\in\mathbb N$, and complex-valued functions $\varphi,f$ on $\mathbb Z\times\mathbb N$ given pointwise by $\varphi(a,s)=[\,2a+s=k+2j\,]\,W_Q(k,s)$ and $f(a,s)=\sum_{e}c_e\,q^{e_1}q^{-\ell j}\,[\,2a+s=e_0+2e_1\,]\,W_q(e_0,s)$, the sum being over the support of the two-variable polynomial `univWord` $(\ell-1)\,k\,j$, namely $S_{\ell}(X_0,X_1)^k\,(X_1^{\ell})^{j}$ with $c_e$ its coefficients, where $S_0=2$, $S_1=X_0$ and $S_{n+2}=X_0S_{n+1}-X_1S_n$. Fix $d\in\mathbb N$ and $P:\mathbb N\to\mathbb C$ with $P(0)=1$, $P(i)=\bigl(q^{(\ell-1)(i-1)}\sum_{t<\ell}q^{t}\bigr)^{-1}$ for $1\le i\le d$, and $P(i)=0$ for $i>d$. Then for all $r_a,r_b\in\mathbb Z$ the twisted shell value equals $\ell$ times the untwisted one: both sides vanish unless $r_a+r_b=k+2j$, and under that condition, when $r_a=r_b$, $$\sum_{m=1}^{r_a^{+}+d}\ell m\,(q^{\ell})^{m}\bigl(1-q^{-\ell}\bigr)\Bigl[\varphi(r_a,0)P(m)+\sum_{i=0}^{\min(d,m-1)}\bigl(P(i)-P(i+1)\bigr)\varphi\bigl(r_a-(m-i),2(m-i)\bigr)\Bigr]$$ equals $\ell$ times $f(\ell r_a,0)\sum_{s=1}^{d}s\,q^{s}(1-q^{-1})+\sum_{i=1}^{\ell r_a^{+}}(d+i)q^{d+i}(1-q^{-1})f(\ell r_a-i,2i)$, while when $r_a\ne r_b$, writing $\mu=\min(r_a,r_b)$ and $\delta=|r_a-r_b|$, $\sum_{m=1}^{\mu^{+}}\ell m\,(q^{\ell})^{m}(1-q^{-\ell})\,\varphi(\mu-m,\delta+2m)$ equals $\ell\sum_{i=1}^{\ell\mu^{+}}i\,q^{i}(1-q^{-1})f(\ell\mu-i,\ell\delta+2i)$; here $(\cdot)^{+}$ denotes truncation of an integer to $\mathbb N$, and all subtractions inside $\varphi$'s natural-number arguments are truncated.
--
--   This is the uniform form, valid for an arbitrary pair of integer valuations $(r_a,r_b)$, of the comparison between a twisted shell sum attached to walk counts for the residue field of size $q^{\ell}$ and the corresponding base-change shell sum attached to walk counts for size $q$; the factor $\ell$ is the degree of the unramified extension. It is used in the inert-place step of the comparison of twisted weighted integrals with weighted Hecke-word integrals, via [`AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank`](thm.html#AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SatakeCombination_twistedShellValue_eq_mul_shellValue.lean

import Mathlib
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.SatakeCombination.twistedShellValue_eq_mul_shellValue
    (q ℓ : ℕ) (hq : 1 ≤ q) (hℓ : 1 ≤ ℓ)
    (Wq : ℕ → ℕ → ℕ) (hWq00 : Wq 0 0 = 1) (hWq0s : ∀ s : ℕ, Wq 0 (s + 1) = 0)
    (hWqroot : ∀ n : ℕ, Wq (n + 1) 0 = (q + 1) * Wq n 1)
    (hWqstep : ∀ n s : ℕ, Wq (n + 1) (s + 1) = Wq n s + q * Wq n (s + 2))
    (WQ : ℕ → ℕ → ℕ) (hWQ00 : WQ 0 0 = 1) (hWQ0s : ∀ s : ℕ, WQ 0 (s + 1) = 0)
    (hWQroot : ∀ n : ℕ, WQ (n + 1) 0 = (q ^ ℓ + 1) * WQ n 1)
    (hWQstep : ∀ n s : ℕ, WQ (n + 1) (s + 1) = WQ n s + q ^ ℓ * WQ n (s + 2))
    (k j : ℕ)
    (φ : ℤ → ℕ → ℂ)
    (hφ : ∀ (a : ℤ) (s : ℕ), φ a s = if 2 * a + s = (k : ℤ) + 2 * j then (WQ k s : ℂ) else 0)
    (f : ℤ → ℕ → ℂ)
    (hf : ∀ (a : ℤ) (s : ℕ), f a s =
      ∑ e ∈ (AutomorphicForm.SatakeCombination.univWord (ℓ - 1) k j).support,
        (AutomorphicForm.SatakeCombination.univWord (ℓ - 1) k j).coeff e * (q : ℂ) ^ (e 1) / (q : ℂ) ^ (ℓ * j) *
          (if 2 * a + s = (e 0 : ℤ) + 2 * (e 1 : ℤ) then (Wq (e 0) s : ℂ) else 0))
    (d : ℕ)
    (P : ℕ → ℂ) (hP0 : P 0 = 1)
    (hP : ∀ i : ℕ, 1 ≤ i → i ≤ d →
      P i = ((q : ℂ) ^ ((ℓ - 1) * (i - 1)) * ∑ t ∈ Finset.range (ℓ), (q : ℂ) ^ t)⁻¹)
    (hPd : ∀ i : ℕ, d < i → P i = 0)
    (ra rb : ℤ) :
    (if ra + rb = (k : ℤ) + 2 * j then
        (if ra = rb then
          ∑ m ∈ Finset.Icc 1 (ra.toNat + d),
            (ℓ : ℂ) * m * ((q : ℂ) ^ (ℓ)) ^ m * (1 - ((q : ℂ) ^ (ℓ))⁻¹) *
              (φ ra 0 * P m +
                ∑ i ∈ Finset.range (min d (m - 1) + 1),
                  (P i - P (i + 1)) * φ (ra - ((m - i : ℕ) : ℤ)) (2 * (m - i)))
        else
          ∑ m ∈ Finset.Icc 1 (min ra rb).toNat,
            (ℓ : ℂ) * m * ((q : ℂ) ^ (ℓ)) ^ m * (1 - ((q : ℂ) ^ (ℓ))⁻¹) *
              φ (min ra rb - m) ((ra - rb).natAbs + 2 * m))
      else 0) =
      (ℓ : ℂ) * (if ra + rb = (k : ℤ) + 2 * j then
        (if ra = rb then
          f ((ℓ : ℤ) * ra) 0 * ∑ s ∈ Finset.Icc 1 d, (s : ℂ) * (q : ℂ) ^ s * (1 - (q : ℂ)⁻¹) +
            ∑ i ∈ Finset.Icc 1 (ℓ * ra.toNat),
              ((d + i : ℕ) : ℂ) * (q : ℂ) ^ (d + i) * (1 - (q : ℂ)⁻¹) * f ((ℓ : ℤ) * ra - i) (2 * i)
        else
          ∑ i ∈ Finset.Icc 1 (ℓ * (min ra rb).toNat),
            (i : ℂ) * (q : ℂ) ^ i * (1 - (q : ℂ)⁻¹) *
              f ((ℓ : ℤ) * min ra rb - i) (ℓ * (ra - rb).natAbs + 2 * i))
      else 0) := by sorry
