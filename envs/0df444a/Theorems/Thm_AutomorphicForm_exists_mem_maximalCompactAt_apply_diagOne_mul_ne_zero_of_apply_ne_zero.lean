-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero
-- name    : AutomorphicForm.exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/8da093b3-a11e-5acf-aa6b-ec3dec3da560
-- title:
--   Iwasawa normalisation of a non-vanishing Whittaker value
-- statement:
--   Let $F$ be a number field, $S$ a finite set of nonzero primes of $\mathcal{O}_F$, and $W$ a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_F)$, where $\mathbb{A}_F$ is the adele ring of $F$. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ and $\omega$ a homomorphism from the idele group $\mathbb{A}_F^{\times}$ to $\mathbb{C}^{\times}$. Assume the two equivariance laws $W\bigl(\begin{pmatrix}1&u\\0&1\end{pmatrix}g\bigr)=\psi(u)\,W(g)$ for all $u \in \mathbb{A}_F$ and all $g$, and $W(z I_2\, g)=\omega(z)\,W(g)$ for all ideles $z$ and all $g$, the second through the central scalar embedding. Let $g_0 \in \mathrm{GL}_2(\mathbb{A}_F)$ be such that for every prime $v \notin S$ and all indices $i,j$, the component at $v$ of the finite part of the entry $(g_0)_{ij}$ agrees with that of the identity matrix, and suppose $W(g_0) \neq 0$. Then there are an idele $t$ and an element $k$ of `maximalCompactAt F S` — that is, the finite part of $k$ lies in `finiteIntegralGL2`, each archimedean component of $k$ is a row isometry, and the component of $k$ at every prime $v \notin S$ is trivial — such that the component at $v$ of the finite part of $t$ equals $1$ for every $v \notin S$, and $W\bigl(\mathrm{diag}(t,1)\,k\bigr) \neq 0$.
--
--   This is the normalisation step supplied by the adelic Iwasawa decomposition $\mathrm{GL}_2(\mathbb{A}_F)=B(\mathbb{A}_F)\mathbf{K}$: a point where a Whittaker-type function with given central and unipotent behaviour is nonzero, and which is trivial away from $S$, may be moved to the form $\mathrm{diag}(t,1)k$ with $k$ in the compact group attached to $S$ and the infinite places and $t$ trivial outside $S$. It is used in the construction of test data for the Rankin–Selberg integral and in the non-vanishing statement for Whittaker coefficients of smooth cusp realisations, and it cites the Iwasawa factorisation [`AutomorphicForm.exists_mem_adelicBorel_mul_eq`](thm.html#AutomorphicForm.exists_mem_adelicBorel_mul_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (W : AdelicGL2 (𝓞 F) F → ℂ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), W (unipotentGL2 u * g) = ψ u * W g)
    (hZ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      W (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ i j : Fin 2,
      ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
        ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v)
    (hW : W g₀ ≠ 0) :
    ∃ (t : (AdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F),
      k ∈ maximalCompactAt F S ∧
      (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1) ∧
      W (diagOne t * k) ≠ 0 := by sorry
