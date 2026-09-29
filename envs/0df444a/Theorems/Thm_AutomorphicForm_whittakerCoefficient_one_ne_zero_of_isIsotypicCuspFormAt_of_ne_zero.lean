-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero
-- name    : AutomorphicForm.whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/186e146d-decd-5d89-adb9-5df81bb25f0b
-- title:
--   Non-vanishing of the first Whittaker coefficient over ℚ
-- statement:
--   Fix a set $D \subseteq \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ and build the carrier data `productionPinsOf ℚ` from it, whose level groups at an ideal $N$ are `levelOne (𝓞 ℚ) ℚ N` intersected with `finiteAdelicGL2Subgroup ℚ` (the kernel of the archimedean projection `glArch`), whose Hecke generators are `heckeGen (𝓞 ℚ) ℚ v`, whose central subgroup is all of $\mathbb{A}_{\mathbb{Q}}^{\times}$, whose measure on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ is the adelic Haar measure, and whose measure $\nu$ on $\mathbb{A}_{\mathbb{Q}}$ is the adelic additive Haar measure conditioned on the box `adelicBox ℚ`. Let $\xi$ be a character of that central subgroup with values in $\mathbb{C}^{\times}$, $N$ an ideal of $\mathbb{Z}$, $S$ a finite set of finite places, $\Phi$ a Hecke eigensystem over $\mathbb{C}$ (a nonzero level ideal together with families $a, b$ of complex numbers indexed by the finite places), and $\varphi : \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$. Assume `IsIsotypicCuspFormAt` holds for these data, i.e. $\varphi$ is a smooth cuspidal automorphic function at these pins for $\xi$ (cuspidality together with $K_f$-smoothness), $\varphi$ is continuous, $\varphi$ is right invariant under the level group at $N$, for every $v \notin S$ the function $\varphi$ is a Hecke coset eigenfunction for that level group and the generator at $v$, with eigenvalue $\Phi.a\,v$, and for every $v \notin S$ one has $\varphi(\mathrm{scalar}(\det \mathrm{gen}_v)\,g) = (\mathrm{cNorm}\,v)^{-1}\,\Phi.b\,v \cdot \varphi(g)$ for all $g$. Assume further $\varphi \neq 0$. Then the first Whittaker coefficient of $\varphi$ for the standard additive character `psiQ`, namely the function $g \mapsto \int \varphi(n(x)g)\,\psi_{\mathbb{Q}}(-x)\,d\nu(x)$ with $n(x)$ the upper unipotent matrix, is not the zero function.
--
--   This is the non-vanishing of the first Fourier–Whittaker coefficient of a nonzero cuspidal $\mathrm{GL}_2$ automorphic form over $\mathbb{Q}$, in the form needed to attach a Whittaker model, and hence an $L$-function, to the form; no summability of the Fourier expansion along the unipotent radical is assumed among the hypotheses. It is used in the construction of finite Whittaker expansions of isotypic cusp forms and in the Rankin–Selberg analysis of the associated $L$-functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm

theorem AutomorphicForm.whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (ξ : (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
      (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
      (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Φ φ)
    (hφ : φ ≠ 0) :
    whittakerCoefficient ℚ (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
      (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 ≠ 0 := by sorry
