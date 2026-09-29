-- Prove2me | Theorems.Thm_CuspForm_exists_eq_rescaleLin_add_rescaleLin_of_heckeTLin_eq_smul_of_exists_level
-- name    : CuspForm.exists_eq_rescaleLin_add_rescaleLin_of_heckeTLin_eq_smul_of_exists_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/6d450dfb-48dc-58ca-82e7-cb96939b881a
-- title:
--   Oldforms at p∤ M in weight two: eigensystem descent
-- statement:
--   Let $M$ and $p$ be natural numbers with $M\neq 0$, $p$ prime, $Mp\neq 0$ and $p\nmid M$, and fix divisibility witnesses $1\cdot M\mid Mp$ and $p\cdot M\mid Mp$. Let $S$ be a finite set of natural numbers and $a:\mathbb{N}\to\mathbb{C}$ a function. Let $f$ be a weight-two cusp form for $\Gamma_0(Mp)$ such that for every prime $\ell$ with $\ell\nmid Mp$ and $\ell\notin S$ one has $T_\ell f=a(\ell)\,f$, where $T_\ell$ denotes the linear operator [`CuspForm.heckeTLin`](def/ModularForm_HeckeOperatorForms.html#L69) in weight two, given by `heckeU` plus the weight-two slash action of $\operatorname{diag}(\ell,1)$. Assume moreover that the eigensystem $(a(\ell))$ already occurs in weight two at level $M$: there is a nonzero cusp form $g$ for $\Gamma_0(M)$ with $T_\ell g=a(\ell)\,g$ for every prime $\ell$ with $\ell\nmid M$, $\ell\nmid Mp$ and $\ell\notin S$. The conclusion is that there exist weight-two cusp forms $h_1,h_2$ for $\Gamma_0(M)$ such that $T_\ell h_1=a(\ell)\,h_1$ and $T_\ell h_2=a(\ell)\,h_2$ for all primes $\ell$ with $\ell\nmid M$, $\ell\nmid Mp$, $\ell\notin S$, and such that $f$ is the sum of the images of $h_1$ and $h_2$ under the degeneracy maps [`FreyPackage.ModMCarrier.rescaleLin`](def/FreyPackage_ModMCarrier_Rescale.html#L140), namely the weight-two slash actions by $\operatorname{diag}(1,1)$ and by $\operatorname{diag}(p,1)$; classically, $f(\tau)=h_1(\tau)+p\,h_2(p\tau)$.
--
--   This is the eigensystem form of Atkin–Lehner theory of oldforms at a prime not dividing the level: an eigenvector in $S_2(\Gamma_0(Mp))$ whose eigenvalues away from a finite set already occur at level $M$ lies in the span of the two degeneracy images of the corresponding eigenspace at level $M$. It feeds the level-lowering step at $p$, being used by [`CohCarrier.exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul`](thm.html#CohCarrier.exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_eq_rescaleLin_add_rescaleLin_of_heckeTLin_eq_smul_of_exists_level.lean

import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem CuspForm.exists_eq_rescaleLin_add_rescaleLin_of_heckeTLin_eq_smul_of_exists_level
    (M p : ℕ) [NeZero M] [Fact p.Prime] [NeZero (M * p)] (hpM : ¬ p ∣ M)
    (h1 : 1 * M ∣ M * p) (hp : p * M ∣ M * p)
    (S : Finset ℕ) (a : ℕ → ℂ)
    (f : CuspForm (Gamma0 (M * p)) 2)
    (hf : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M * p), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN f = a ℓ • f)
    (hocc : ∃ g : CuspForm (Gamma0 M) 2, g ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (_ : ¬ ℓ ∣ M * p), ℓ ∉ S →
        CuspForm.heckeTLin 2 hℓ hℓM g = a ℓ • g) :
    ∃ h₁ h₂ : CuspForm (Gamma0 M) 2,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (_ : ¬ ℓ ∣ M * p), ℓ ∉ S →
        CuspForm.heckeTLin 2 hℓ hℓM h₁ = a ℓ • h₁ ∧ CuspForm.heckeTLin 2 hℓ hℓM h₂ = a ℓ • h₂) ∧
      f = FreyPackage.ModMCarrier.rescaleLin h1 2 h₁ + FreyPackage.ModMCarrier.rescaleLin hp 2 h₂ := by sorry
