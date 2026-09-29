-- Prove2me | Theorems.Thm_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_unipotentEdgeMoment_eq_mul_sum_laurentCoeff_edge
-- name    : AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_unipotentEdgeMoment_eq_mul_sum_laurentCoeff_edge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/5b81fed1-ddc0-5389-90b2-295a307e4fb1
-- title:
--   Slot combination of unipotent edge moments at one place
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $ws$ assign to every height-one prime $v$ of $\mathcal O_K$ an element of $v.\mathrm{Extension}(\mathcal O_L)$, that is, a height-one prime $(ws\,v)_1$ of $\mathcal O_L$ whose contraction to $\mathcal O_K$ is $v$. Fix a height-one prime $v$ of $\mathcal O_K$, a height-one prime $w'$ of $\mathcal O_L$, complex numbers $\xi,\zeta,\sigma_r,s$, and natural numbers $k,j$. Write $f = \mathrm{slotDeg}\,K\,L\,ws\,v$ for the inertia degree `inertiaDeg'` of $v.\mathrm{asIdeal}$ in $(ws\,v)_1.\mathrm{asIdeal}$. Assume $\sigma_r^2 = N(v)\,\xi$, where $N(v)$ denotes the absolute norm of $v.\mathrm{asIdeal}$ viewed in $\mathbb C$ (the quantity `HeckeEigensystem.cNorm v`); assume $\sqrt{N(w')}\,s = \sigma_r^{f}$, where $N(w')$ is the absolute norm of $w'.\mathrm{asIdeal}$; assume $\xi^{f} = \zeta$; and assume $N((ws\,v)_1) = N(v)^{f}$. The slot word at $v$ is the two-variable polynomial $W = \mathrm{satakePow}\,((f-1)+1)\,(X_0)\,(X_1)^{k}\cdot (X_1^{(f-1)+1})^{j}$ in $\mathbb C[X_0,X_1]$ (truncated natural subtraction), and the slot coefficient at a monomial exponent $r \in \mathrm{Fin}\,2 \to_0 \mathbb N$ is $W_r\,N(v)^{r(1)}/N((ws\,v)_1)^{j}$. The assertion is the identity
--   $$\sum_{r \in \mathrm{supp}(W)} \frac{W_r\,N(v)^{r(1)}}{N((ws\,v)_1)^{j}}\,\bigl(1+(-1)^{r(0)}\bigr)\bigl(4\,N(v)\xi\bigr)^{\lfloor r(0)/2\rfloor}\xi^{r(1)} = \bigl(\sqrt{N(w')}\,s\bigr)^{k}\zeta^{j}\sum_{n=-k}^{k} \bigl[(T^{1}+T^{-1})^{k}\bigr]_n\bigl(1+(-1)^{f\,|n|}\bigr),$$
--   the exponent $\lfloor r(0)/2\rfloor$ being natural division and the inner coefficients being those of the Laurent polynomial $(T^{1}+T^{-1})^{k}$ over $\mathbb C$, summed over $n$ in the integer interval $[-k,k]$.
--
--   This is the place-wise evaluation of a slot word against the "edge" functional $P \mapsto P(1)+P(-1)$ on $\mathbb C[t^{\pm 1}]$, the companion of the corresponding constant-coefficient identity: it rewrites the weighted sum of edge moments at a single place as a Laurent-coefficient sum depending only on $k$ and the inertia degree $f$. It is used in the assembly of the explicit unipotent term, [`AutomorphicForm.sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge`](thm.html#AutomorphicForm.sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_unipotentEdgeMoment_eq_mul_sum_laurentCoeff_edge.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_unipotentEdgeMoment_eq_mul_sum_laurentCoeff_edge
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) (w' : HeightOneSpectrum (𝓞 L))
    (ξ ζ σr s : ℂ)
    (hσ : σr ^ 2 = HeckeEigensystem.cNorm v * ξ)
    (hs : ((Real.sqrt (Ideal.absNorm w'.asIdeal : ℝ) : ℂ) * s) = σr ^ SatakeCombination.slotDeg K L ws v)
    (hζ : ξ ^ SatakeCombination.slotDeg K L ws v = ζ)
    (hNws : Ideal.absNorm (ws v).1.asIdeal = Ideal.absNorm v.asIdeal ^ SatakeCombination.slotDeg K L ws v)
    (k j : ℕ) :
    ∑ r ∈ (SatakeCombination.slotWord K L ws v k j).support,
      SatakeCombination.slotCoeff K L ws v k j r *
        ((1 + (-1 : ℂ) ^ r 0) * (4 * (HeckeEigensystem.cNorm v * ξ)) ^ (r 0 / 2) * ξ ^ r 1) =
      ((Real.sqrt (Ideal.absNorm w'.asIdeal : ℝ) : ℂ) * s) ^ k * ζ ^ j *
        ∑ n ∈ Finset.Icc (-(k : ℤ)) k,
          ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff n *
            (1 + (-1 : ℂ) ^ (SatakeCombination.slotDeg K L ws v * n.natAbs)) := by sorry
