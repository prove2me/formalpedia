-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_not_exists_forall_apply_mul_heckeGen_eq_of_continuous
-- name    : AutomorphicForm.SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/91b39f7f-81a1-5967-aa9e-05e3d35e7c23
-- title:
--   Continuous cuspidal realisations are not translation eigenvectors at v
-- statement:
--   Let $\Psi$ be a complex Hecke eigensystem over $\mathbb{Q}$: a nonzero ideal $\Psi.\mathrm{level}$ of $\mathcal{O}_{\mathbb{Q}}$ together with families $a,b$ of complex numbers indexed by the height one primes. Let $R$ be a smooth cuspidal realisation of $\Psi$ on the general production pins of $\mathbb{Q}$, that is, the carrier pins `productionPinsGeneral` built from the class-representative Siegel set with parameters $c=1/2$, $u=1$, $d_1=1/2$, $d_2=2$, the level groups $N \mapsto \mathrm{levelOne}(N) \sqcap \mathrm{finiteAdelicGL2Subgroup}$, the generators $v \mapsto$ `heckeGen`$(v)$ and the adelic box: so $R$ consists of a function $\varphi = R.\mathrm{toFun}$ on $GL_2(\mathbb{A}_{\mathbb{Q}})$ which is not identically zero, a character of the central subgroup of the pins, a proof that $\varphi$ is cuspidal automorphic for that central character and `IsKfSmooth`, right invariance of $\varphi$ under the level subgroup attached to $\Psi.\mathrm{level}$, a finite exceptional set of primes, Hecke coset eigenrelations with eigenvalues $\Psi.a(w)$ outside it, and central eigenrelations with $\Psi.b(w)$. Assume $\varphi$ is continuous, and let $v$ be a height one prime with $v$ not dividing $\Psi.\mathrm{level}$. Then there is no $c \in \mathbb{C}$ with $\varphi(g\cdot h_v) = c\,\varphi(g)$ for all $g \in GL_2(\mathbb{A}_{\mathbb{Q}})$, where $h_v =$ `heckeGen`$(v)$ is the image of a uniformizer of the completion at $v$ under the homomorphism $x \mapsto \mathrm{diag}(x,1)$ placed at the place $v$ and the identity elsewhere.
--
--   The statement records that a continuous cuspidal realisation cannot be a one-dimensional eigenvector for right translation by the element $\mathrm{diag}(\varpi_v,1)$ at a prime away from the level: classically a reflection of the fact that the local component at such a place is an infinite-dimensional representation, visible in the Kirillov model where $\mathrm{diag}(a,1)$ acts by dilation on functions on $\mathbb{Q}_v^\times$ supported away from $0$. It is used in the converse direction of the Langlands–Tunnell part of the development, via [`LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable`](thm.html#LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable); the proof invokes the generation of $SL_2$ of a field by diagonal, upper unipotent and Weyl elements together with density of $\mathbb{Q}$ plus the single completion at $v$ in the adeles of $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_not_exists_forall_apply_mul_heckeGen_eq_of_continuous.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous
    (Ψ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (R : AutomorphicForm.SmoothCuspRealizationAt ℚ (AutomorphicForm.productionPinsGeneral ℚ) Ψ)
    (hR : AutomorphicForm.IsGenuineCuspRealizationAt ℚ (AutomorphicForm.productionPinsGeneral ℚ) Ψ R)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hv : ¬ v.asIdeal ∣ Ψ.level) :
    ¬ ∃ c : ℂ, ∀ g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      R.toFun (g * NumberField.AdelicLevel.heckeGen (NumberField.RingOfIntegers ℚ) ℚ v) = c * R.toFun g := by sorry
