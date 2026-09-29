-- Prove2me | Theorems.Thm_CohCarrier_exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int
-- name    : CohCarrier.exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/9f775c7c-3cea-5db0-aad1-1c9cb7ffdb58
-- title:
--   Deligne–Serre lifting for Hecke eigenclasses on Γ_H(N)
-- statement:
--   Fix a prime $p$, an integer $N \neq 0$, a subgroup $H \le (\mathbb{Z}/N)^\times$ and a set $S_0 \subseteq \mathbb{N}$, and write $\Gamma_H(N)$ for the subgroup [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$ obtained by taking the matrices of $\Gamma_0(N)$ whose associated unit of $\mathbb{Z}/N$ lies in $H$; for an abelian group $A$, [`CohCarrier.H1 N H A`](def/CohCarrier_Level.html#L162) is the group of additive homomorphisms from $\Gamma_H(N)$, written additively, to $A$, and for $\ell \neq 0$ the operator [`CohCarrier.heckeT N H ℓ A`](def/CohCarrier_Level.html#L250) is the transfer to $\Gamma_H(N)$ of the homomorphism obtained by precomposing with the conjugation map [`CohCarrier.conjL`](def/CohCarrier_Level.html#L228). Let $\kappa$ be a field of characteristic $p$, let $\varphi$ be a ring homomorphism from the ring $\overline{\mathbb{Z}}$ of algebraic integers in $\mathbb{C}$ (the integral closure of $\mathbb{Z}$ in $\mathbb{C}$) to $\kappa$, and let $\mathrm{lam} : \mathbb{N} \to \kappa$. Assume $x : \Gamma_H(N) \to \kappa$ is a nonzero homomorphism lying in the $\kappa$-span of the homomorphisms obtained from integral ones $G : \Gamma_H(N) \to \mathbb{Z}$ by composing with $\mathbb{Z} \to \kappa$, and that $T_\ell x = \mathrm{lam}(\ell)\, x$ for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S_0$. Then there exist a nonzero homomorphism $X : \Gamma_H(N) \to \mathbb{C}$, a family $\theta : \mathbb{N} \to \overline{\mathbb{Z}}$ and a ring homomorphism $\varphi' : \overline{\mathbb{Z}} \to \kappa$ such that $T_\ell X = \theta(\ell)\, X$ and $\varphi'(\theta(\ell)) = \mathrm{lam}(\ell)$ for all primes $\ell \nmid N$ with $\ell \notin S_0$. The homomorphism $\varphi'$ produced is not required to agree with the given $\varphi$.
--
--   This is the Deligne–Serre lifting lemma in the form needed for group cohomology of $\Gamma_H(N)$ with the lattice $\mathrm{Hom}(\Gamma_H(N),\mathbb{Z})$: a system of Hecke eigenvalues in characteristic $p$ carried by a class coming from the integral lattice is the reduction, along some embedding of the algebraic integers into $\kappa$, of a system of eigenvalues occurring in $\mathrm{Hom}(\Gamma_H(N),\mathbb{C})$. It feeds the construction of a Galois representation with prescribed traces attached to a weight-two eigensystem modulo $p$, via [`GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom`](thm.html#GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int.lean

import Mathlib
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (S₀ : Set ℕ)
    (κ : Type) [Field κ] [CharP κ p] (φ : integralClosure ℤ ℂ →+* κ) (lam : ℕ → κ)
    (x : CohCarrier.H1 N H κ) (hx0 : x ≠ 0)
    (hx : x ∈ Submodule.span κ
      (Set.range fun G : CohCarrier.H1 N H ℤ => (Int.castAddHom κ).comp G))
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT N H ℓ κ x) = lam ℓ • x) :
    ∃ (X : CohCarrier.H1 N H ℂ) (θ : ℕ → integralClosure ℤ ℂ) (φ' : integralClosure ℤ ℂ →+* κ),
      X ≠ 0 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT N H ℓ ℂ X) =
          ((θ ℓ : integralClosure ℤ ℂ) : ℂ) • X) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → φ' (θ ℓ) = lam ℓ) := by sorry
