-- Prove2me | Theorems.Thm_Fin_exists_forall_vertexLaw_and_edgeLaw_pow_of_pow_add_of_modEq_of_forall_flow_sum_mul_eq
-- name    : Fin.exists_forall_vertexLaw_and_edgeLaw_pow_of_pow_add_of_modEq_of_forall_flow_sum_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/05dc570e-de54-5a10-ac92-b5b8293ff0f3
-- title:
--   Uniform ℓ-power bound for integral tropical principality
-- statement:
--   Fix natural numbers $n$ and $m$, maps $\mathrm{src},\mathrm{tgt} : \mathrm{Fin}\,m \to \mathrm{Fin}\,n$ (an oriented multigraph on $n$ vertices with $m$ edges, loops and parallel edges allowed), a weight function $w : \mathrm{Fin}\,m \to \mathbb{N}$ with $w(e) > 0$ for every edge $e$, and a natural number $\ell > 1$. The assertion is that there exists $N \in \mathbb{N}$ such that for all $k \in \mathbb{N}$ and all integer-valued data $d : \mathrm{Fin}\,n \to \mathbb{Z}$, $M, \tau : \mathrm{Fin}\,m \to \mathbb{Z}$, $\varphi : \mathrm{Fin}\,n \to \mathbb{Z}$ and $\sigma' : \mathrm{Fin}\,m \to \mathbb{Z}$ the following holds. Assume: (i) $\tau(e) \equiv \varphi(\mathrm{tgt}\,e) - \varphi(\mathrm{src}\,e) \pmod{\ell^{k+N}}$ for every edge $e$; (ii) with $q = \ell^{k+N}$, the vertex law $q\,d(i) + \sum_{\mathrm{src}\,e = i} \sigma'(e) + \sum_{\mathrm{tgt}\,e = i} (q\,M(e) - \sigma'(e)) = 0$ holds at every vertex $i$; (iii) for every $\varepsilon : \mathrm{Fin}\,m \to \mathbb{Z}$ with zero divergence, i.e. $\sum_{\mathrm{src}\,e = i} \varepsilon(e) = \sum_{\mathrm{tgt}\,e = i} \varepsilon(e)$ for all $i$, one has $\sum_e \varepsilon(e)\,q\,\tau(e) = \sum_e \varepsilon(e)\,q\,w(e)\,(q\,M(e) - \sigma'(e))$. Then there exist $\sigma : \mathrm{Fin}\,m \to \mathbb{Z}$ and $\alpha : \mathrm{Fin}\,n \to \mathbb{Z}$ such that the vertex law holds with $q$ replaced by $\ell^{N}$ and $\sigma'$ by $\sigma$, and moreover the edge law $\alpha(\mathrm{src}\,e) + \ell^{N}\tau(e) = \alpha(\mathrm{tgt}\,e) + \ell^{k+N} w(e)\,(\ell^{N} M(e) - \sigma(e))$ holds for every edge $e$. Note that $N$ depends only on $n$, $m$, $\mathrm{src}$, $\mathrm{tgt}$, $w$ and $\ell$, not on $k$ or on the data $(d, M, \tau, \varphi, \sigma')$.
--
--   This is the combinatorial statement that the integral tropical Jacobian (critical group) of a finite length-weighted graph has $\ell$-primary part of bounded exponent: a configuration whose $\ell^{k+N}$-th multiple satisfies the vertex law and the edge law paired against all integral flows (so that the vertex potentials drop out) already has its $\ell^{N}$-th multiple tropically principal with integer potentials, uniformly in $k$. It is used in the analysis of invariants of the rational Tate module attached to a semistable covering, where a class has to be rearranged into an explicitly chart-supported representative.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Fin_exists_forall_vertexLaw_and_edgeLaw_pow_of_pow_add_of_modEq_of_forall_flow_sum_mul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Fin.exists_forall_vertexLaw_and_edgeLaw_pow_of_pow_add_of_modEq_of_forall_flow_sum_mul_eq
    (n m : ℕ) (src tgt : Fin m → Fin n) (w : Fin m → ℕ) (hw : ∀ e, 0 < w e) (ℓ : ℕ) (hℓ : 1 < ℓ) :
    ∃ N : ℕ, ∀ (k : ℕ) (d : Fin n → ℤ) (M τ : Fin m → ℤ) (φ : Fin n → ℤ) (σ' : Fin m → ℤ),
      (∀ e : Fin m, τ e ≡ φ (tgt e) - φ (src e) [ZMOD ((ℓ : ℤ) ^ (k + N))]) →
      (∀ i : Fin n, (ℓ : ℤ) ^ (k + N) * d i + (∑ e, if src e = i then σ' e else 0) +
          (∑ e, if tgt e = i then (ℓ : ℤ) ^ (k + N) * M e - σ' e else 0) = 0) →
      (∀ ε : Fin m → ℤ,
        (∀ i : Fin n, (∑ e, if src e = i then ε e else 0) = (∑ e, if tgt e = i then ε e else 0)) →
        (∑ e, ε e * ((ℓ : ℤ) ^ (k + N) * τ e)) =
          ∑ e, ε e * ((ℓ : ℤ) ^ (k + N) * (w e : ℤ) * ((ℓ : ℤ) ^ (k + N) * M e - σ' e))) →
      ∃ (σ : Fin m → ℤ) (α : Fin n → ℤ),
        (∀ i : Fin n, (ℓ : ℤ) ^ N * d i + (∑ e, if src e = i then σ e else 0) +
            (∑ e, if tgt e = i then (ℓ : ℤ) ^ N * M e - σ e else 0) = 0) ∧
        (∀ e : Fin m, α (src e) + (ℓ : ℤ) ^ N * τ e =
            α (tgt e) + (ℓ : ℤ) ^ (k + N) * (w e : ℤ) * ((ℓ : ℤ) ^ N * M e - σ e)) := by sorry
