-- Prove2me | Theorems.Thm_CuspForm_exists_isEigenformWith_qCoeff_eq_of_heckeTLinH_eq_smul_of_heckeULinH_eq_smul_of_diamondLinH_eq_smul
-- name    : CuspForm.exists_isEigenformWith_qCoeff_eq_of_heckeTLinH_eq_smul_of_heckeULinH_eq_smul_of_diamondLinH_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/f0cc3703-2ac5-579d-9d3c-c64307a0a6cf
-- title:
--   From Γ_H(M) eigenvectors to normalised eigenforms on Γ₁(M)
-- statement:
--   Let $M\ge 1$, let $H\le(\mathbb Z/M)^\times$ be a subgroup, $k\in\mathbb Z$, and let $S,Q\subseteq\mathbb N$ with every $q\in Q$ dividing $M$. Let $a,b\colon\mathbb N\to\mathbb C$ be functions and $e\colon(\mathbb Z/M)^\times\to\mathbb C^\times$ a group homomorphism. Let $f\neq 0$ be a cusp form of weight $k$ for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}_2(\mathbb Z)$ of the subgroup of $\Gamma_0(M)$ whose lower-right entry reduces into $H$. Assume: for every prime $\ell\notin S$ with $\ell\nmid M$, $f$ is an eigenvector of [`CuspForm.heckeTLinH`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224) with eigenvalue $a(\ell)$, that operator being $g\mapsto U_\ell g+g\mid_k\bigl(\sigma_\ell\,\mathrm{diag}(\ell,1)\bigr)$ with $\sigma_\ell\in\Gamma_0(M)$ a lift of $\ell$ (and $0$ if the relevant stability predicate `StableT` fails); for every $q\in Q$, [`CuspForm.heckeULinH k q`](def/CuspForm_HeckeOperatorFormsGammaH.html#L171) sends $f$ to $b(q)\cdot f$, this operator being induced by $U_q$, $g\mapsto\sum_{j<q}g\mid_k\begin{pmatrix}1&j\\0&q\end{pmatrix}$ (and $0$ if `StableU` fails); and for every $u\in(\mathbb Z/M)^\times$ the diamond operator $g\mapsto g\mid_k\sigma_u$ sends $f$ to $e(u)\cdot f$ (again $0$ if `StableD` fails). Then there are a Dirichlet character $\varepsilon$ modulo $M$ with values in $\mathbb C$ and a cusp form $h$ of weight $k$ for $\Gamma_1(M)$ such that: $\varepsilon$ restricted to units equals $e$; the $q$-expansion coefficients (of width $1$) satisfy $c_1(h)=1$, $c_{pn}(h)+\varepsilon(p)p^{k-1}[p\mid n]c_{n/p}(h)=c_p(h)c_n(h)$ for all primes $p\nmid M$ and all $n$, and $c_{\ell n}(h)=c_\ell(h)c_n(h)$ for all primes $\ell\mid M$ and all $n$; $h(\gamma\tau)=\varepsilon(\gamma_{11})(\gamma_{10}\tau+\gamma_{11})^k h(\tau)$ for all $\gamma\in\Gamma_0(M)$ and $\tau\in\mathbb H$; $c_\ell(h)=a(\ell)$ for all primes $\ell\notin S$ with $\ell\nmid M$; and $c_q(h)=b(q)$ for all $q\in Q$.
--
--   This is the passage from a simultaneous eigenvector of a partial family of Hecke, $U$- and diamond operators on $S_k(\Gamma_H(M))$ to a normalised eigenform on $\Gamma_1(M)$ with nebentypus character, with the eigenvalues recovered as $q$-expansion coefficients; it is a statement about modular forms only. It is used by [`CohCarrier.exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul`](thm.html#CohCarrier.exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul), where Hecke eigenvectors produced on the cohomological side are converted into eigenforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_isEigenformWith_qCoeff_eq_of_heckeTLinH_eq_smul_of_heckeULinH_eq_smul_of_diamondLinH_eq_smul.lean

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_isEigenformWith_qCoeff_eq_of_heckeTLinH_eq_smul_of_heckeULinH_eq_smul_of_diamondLinH_eq_smul
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (S : Set ℕ) (Q : Set ℕ)
    (hQ : ∀ q ∈ Q, q ∣ M) (a b : ℕ → ℂ) (e : (ZMod M)ˣ →* ℂˣ)
    (f : CuspForm (CohCarrier.GammaH M H) k) (hf : f ≠ 0)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (hℓM : ¬ ℓ ∣ M),
      CuspForm.heckeTLinH k hℓ hℓM f = a ℓ • f)
    (hU : ∀ q ∈ Q, CuspForm.heckeULinH k q f = b q • f)
    (hD : ∀ u : (ZMod M)ˣ, CuspForm.diamondLinH k u f = (e u : ℂ) • f) :
    ∃ (ε : DirichletCharacter ℂ M) (h : CuspForm (CongruenceSubgroup.Gamma1 M) k),
      CuspForm.IsEigenformWith ε h ∧
      (∀ u : (ZMod M)ˣ, ε (u : ZMod M) = e u) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M → ModularFormClass.qCoeff h ℓ = a ℓ) ∧
      (∀ q ∈ Q, ModularFormClass.qCoeff h q = b q) := by sorry
