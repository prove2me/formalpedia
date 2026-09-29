-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isOrbitalIntegralOn_and_exists_isTwistedOrbitalIntegralOn_and_eq_of_areMatchingArch_diagUnits2
-- name    : AutomorphicForm.exists_isOrbitalIntegralOn_and_exists_isTwistedOrbitalIntegralOn_and_eq_of_areMatchingArch_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/9a5abfbf-9036-5fc2-8bf9-8eddff40935e
-- title:
--   Archimedean matching at a regular split diagonal element
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ a finite Galois extension, let $\sigma$ be an element of $\mathrm{Gal}(L/K)$ generating it (every automorphism lies in the subgroup of integer powers of $\sigma$), and suppose $[L:K]$ is prime. Let $\varphi_\infty : \mathrm{GL}_2(L\otimes\mathbb{R}) \to \mathbb{C}$ and $f_\infty : \mathrm{GL}_2(K\otimes\mathbb{R})\to\mathbb{C}$ (infinite adele rings) each be an archimedean test factor, i.e. compactly supported and of the form $g \mapsto \Phi$ of the matrix of archimedean entries of $g$ for some $C^\infty$ function $\Phi$ on $2\times 2$ matrices over the mixed space, and assume $\varphi_\infty$ and $f_\infty$ satisfy the matching relation [`AutomorphicForm.AreMatchingArch`](def/AutomorphicForm_TwistedOrbital.html#L427) for $\sigma$, that is `AreMatchingOn` for the pair $(\varphi_\infty\circ\,$`archIdentGL`$, f_\infty)$ with respect to the Haar measures `archHaarL` and `archHaarK`. Let $a,t$ be units of the infinite adele ring of $K$ and put $\gamma = \mathrm{diag}(a, at)$; assume $\gamma$ is regular semisimple in the sense that $\mathrm{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit. Let $\alpha,\beta$ be units of $L\otimes_K (K\otimes\mathbb{R})$, put $\delta = \mathrm{diag}(\alpha,\beta)$, and assume the norm string $\prod_{i<[L:K]}(\sigma\text{-semilinear iterate})^i\delta$ equals the base change of $\gamma$ along $A \to L\otimes_K A$. Let $\tau$ be a Haar measure on the centraliser of $\gamma$ in $\mathrm{GL}_2$ of the infinite adeles of $K$, and $\tau'$ a Haar measure on the $\sigma$-twisted centraliser of $\delta$, both with their Borel $\sigma$-algebras, and assume they are coupled with conjugator $y = 1$: the pushforward of $\tau'$ under conjugation by $1$ coincides with the pushforward of $\tau$ under base change to $L\otimes_K A$. Then there exists $I\in\mathbb{C}$ which is an orbital integral of $f_\infty$ at $\gamma$ against `archHaarK` and $\tau$ (that is, $I = \int f_\infty(x^{-1}\gamma x)\,w(x)$ for some section weight $w$ for $\tau$), there exists $I'\in\mathbb{C}$ which is a twisted orbital integral of $\varphi_\infty\circ\,$`archIdentGL` at $\delta$ against `archHaarL` and $\tau'$ (that is, $I' = \int \varphi_\infty(x^{-1}\delta\,\sigma(x))\,w'(x)$ for some twisted section weight $w'$), and any such $I$ and $I'$ satisfy $I' = I$.
--
--   This is the archimedean instance of the comparison of orbital integrals with twisted orbital integrals in cyclic base change for $\mathrm{GL}_2$, specialised to a regular diagonal element $\mathrm{diag}(a,at)$ and to coupled Haar measures on the centraliser and the twisted centraliser. Existence of the two integrals comes from the existence of continuous section weights on each side, and the resulting equality is used in the assembly of the archimedean discrepancy estimate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isOrbitalIntegralOn_and_exists_isTwistedOrbitalIntegralOn_and_eq_of_areMatchingArch_diagUnits2.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped Classical

theorem AutomorphicForm.exists_isOrbitalIntegralOn_and_exists_isTwistedOrbitalIntegralOn_and_eq_of_areMatchingArch_diagUnits2
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (hmatch : AutomorphicForm.AreMatchingArch K L σ φa fa)
    (a t : (InfiniteAdeleRing K)ˣ) (hreg : AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)))
    (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (hN : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)))
    (τ : @MeasureTheory.Measure
      (Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (diagUnits2 a (a * t))))
    (hτ : @MeasureTheory.Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (diagUnits2 a (a * t))) τ)
    (τ' : @MeasureTheory.Measure
      (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (diagUnits2 α β))
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ (diagUnits2 α β)))
    (hτ' : @MeasureTheory.Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ (diagUnits2 α β)) τ')
    (hcoup : AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (diagUnits2 a (a * t)) (diagUnits2 α β) 1 τ τ') :
    (∃ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K)
      (diagUnits2 a (a * t)) τ fa I) ∧
    (∃ I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L)
      (diagUnits2 α β) τ' (φa ∘ AutomorphicForm.archIdentGL K L) I') ∧
    ∀ I I' : ℂ,
      AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K)
        (diagUnits2 a (a * t)) τ fa I →
      AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L)
        (diagUnits2 α β) τ' (φa ∘ AutomorphicForm.archIdentGL K L) I' →
      I' = I := by sorry
