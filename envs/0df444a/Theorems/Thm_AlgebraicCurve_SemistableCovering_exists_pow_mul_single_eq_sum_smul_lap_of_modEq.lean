-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_pow_mul_single_eq_sum_smul_lap_of_modEq
-- name    : AlgebraicCurve.SemistableCovering.exists_pow_mul_single_eq_sum_smul_lap_of_modEq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/0695a286-cc89-5da9-acd2-4d5e6f780581
-- title:
--   ℓ-power depth divisors are Laplacian potentials after subdivision
-- statement:
--   Fix natural numbers $n$ and $m$, maps $\mathrm{src},\mathrm{tgt} : \mathrm{Fin}\,m \to \mathrm{Fin}\,n$ (the ends of $m$ edges on $n$ vertices), widths $w : \mathrm{Fin}\,m \to \mathbb{N}$ with $w_e \neq 0$ for all $e$, a prime $\ell$, an integer exponent $k > 0$, and target residues $n_0 : \mathrm{Fin}\,m \to \mathbb{Z}$. The assertion is that there exist $K \geq k$ and integers $n_e$ with $\ell^k \mid n_e - n_0(e)$ for every $e$, such that the following holds for the $\ell^K$-subdivision. Put $V := \mathrm{Fin}\,n \sqcup \coprod_e \mathrm{Fin}(\ell^K w_e - 1)$, so that edge $e$ carries $\ell^K w_e - 1$ interior vertices; the segment set is $\coprod_e \mathrm{Fin}(\ell^K w_e)$, and the segment $(e,i)$ has ends $\mathrm{src}(e)$ if $i = 0$ and the interior vertex $(e, i-1)$ otherwise, and $\mathrm{tgt}(e)$ if $i+1 = \ell^K w_e$ and the interior vertex $(e,i)$ otherwise. For $v \in V$, $\mathrm{lap}\,v : V \to \mathbb{Z}$ is the sum over all segments $\varepsilon$ of $\delta_v - \delta_{v'}$ taken once for each end of $\varepsilon$ equal to $v$, with $v'$ the opposite end, i.e. the Laplacian row at $v$. Then there is a potential $\varphi : V \to \mathbb{Z}$ such that, at every interior vertex $\mathrm{Sum.inr}\,v$, the value of $\ell^K \sum_e n_e\,\delta_{(e,\,\ell^{K-k}-1)}$ agrees with the value of $\sum_{u \in V} \varphi(u)\,\mathrm{lap}\,u$. No condition is imposed at the vertices coming from $\mathrm{Fin}\,n$.
--
--   A purely combinatorial lemma about divisors and integral potentials on subdivided graphs in the style of Baker–Norine: a prescribed pattern of multiplicities placed at depth $\ell^{K-k}$ along each edge becomes, after multiplication by $\ell^K$ and a prime-to-$\ell$ adjustment of the multiplicities modulo $\ell^k$, the Laplacian of an integral potential away from the original vertices. It is used in the analysis of semistable coverings of curves, feeding the statement [`AlgebraicCurve.exists_zsmul_mk_eq_zero_eq_add_sum_single_pow_evalAt_param_eq_mul_of_semistableCovering_of_discFibres_of_rankOne_of_isUnit_of_charZero_of_semistableModel`](thm.html#AlgebraicCurve.exists_zsmul_mk_eq_zero_eq_add_sum_single_pow_evalAt_param_eq_mul_of_semistableCovering_of_discFibres_of_rankOne_of_isUnit_of_charZero_of_semistableModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_exists_pow_mul_single_eq_sum_smul_lap_of_modEq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem
    AlgebraicCurve.SemistableCovering.exists_pow_mul_single_eq_sum_smul_lap_of_modEq
    (n m : ℕ) (src tgt : Fin m → Fin n) (w : Fin m → ℕ) (hw : ∀ e, w e ≠ 0)
    (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (hk : 0 < k) (n₀ : Fin m → ℤ) :
    ∃ (K : ℕ) (hK : k ≤ K) (nn : Fin m → ℤ), (∀ e, ((ℓ ^ k : ℕ) : ℤ) ∣ nn e - n₀ e) ∧
    let V := Fin n ⊕ (Σ e : Fin m, Fin (ℓ ^ K * w e - 1))
    let ends : (Σ e : Fin m, Fin (ℓ ^ K * w e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = ℓ ^ K * w ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (ℓ ^ K * w e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    ∃ φ : V → ℤ, ∀ v : Σ e : Fin m, Fin (ℓ ^ K * w e - 1),
      (ℓ ^ K : ℤ) * (∑ e, nn e • (Pi.single (Sum.inr ⟨e, ⟨ℓ ^ (K - k) - 1, by
          have h1 : 1 ≤ ℓ ^ (K - k) := Nat.one_le_pow _ _ (Fact.out : ℓ.Prime).pos
          have h2 : ℓ ^ (K - k) < ℓ ^ K := Nat.pow_lt_pow_right (Fact.out : ℓ.Prime).one_lt (by omega)
          have h3 : ℓ ^ K ≤ ℓ ^ K * w e := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (hw e))
          omega⟩⟩) 1 : V → ℤ)) (Sum.inr v)
        = (∑ u, φ u • lap u) (Sum.inr v) := by sorry
