-- Prove2me | Theorems.Thm_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand
-- name    : EisensteinSeries.exists_modularForm_gamma_apply_eq_tsum_eisSummand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/913ae839-f963-5316-8af9-9829b0214356
-- title:
--   Full-lattice level-N Eisenstein series of weight k≥ 3
-- statement:
--   Let $N$ be a nonzero natural number and $k$ an integer with $3 \le k$. The assertion is the existence of a family $G$, indexed by the vectors $v : \mathrm{Fin}\,2 \to \mathbb{Z}/N$, of modular forms of weight $k$ for the principal congruence subgroup $\Gamma(N)$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$, with two properties. First, for every $v$ and every $\tau$ in the upper half-plane, the value $G_v(\tau)$ is the sum of the (unordered, absolutely convergent) series $\sum_x \mathtt{eisSummand}\,k\,x\,\tau$ taken over the subtype of integral vectors $x : \mathrm{Fin}\,2 \to \mathbb{Z}$ whose componentwise reduction modulo $N$ equals $v$, the summand being $(x_0\tau + x_1)^{-k}$; in particular the vector $x = 0$, which occurs only for $v = 0$, contributes $0$. Second, for every $v$ and every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, the weight-$k$ slash action of the image of $\gamma$ in $\mathrm{GL}_2(\mathbb{R})$ on the function underlying $G_v$ is the function underlying $G_{v\bar\gamma}$, where $v\bar\gamma$ is the row vector $v$ multiplied on the right (`Matrix.vecMul`) by the reduction of the matrix of $\gamma$ modulo $N$.
--
--   These are the classical non-primitive Eisenstein series of weight $k$ and level $N$, summed over a full congruence class of lattice vectors rather than over primitive vectors, together with the index law describing the $\mathrm{SL}_2(\mathbb{Z})$-action on the family. They feed the construction of the weight-three and weight-four forms attached to torsion points on modular curves of full level, via the second derivative of the Weierstrass $\wp$-function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem EisensteinSeries.exists_modularForm_gamma_apply_eq_tsum_eisSummand
    (N : ℕ) [NeZero N] (k : ℤ) (hk : 3 ≤ k) :
    ∃ G : (Fin 2 → ZMod N) → ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ (v : Fin 2 → ZMod N) (τ : UpperHalfPlane),
        G v τ = ∑' x : {x : Fin 2 → ℤ // ((↑) : ℤ → ZMod N) ∘ x = v}, EisensteinSeries.eisSummand k x.1 τ) ∧
      (∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)),
        ((⇑(G v) : UpperHalfPlane → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) =
          ⇑(G (Matrix.vecMul v ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N))))) := by sorry
