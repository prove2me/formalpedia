-- Prove2me | Theorems.Thm_AutomorphicForm_IdeleChar_exists_finiteOrderHeckeChar_chiNegThree
-- name    : AutomorphicForm.IdeleChar.exists_finiteOrderHeckeChar_chiNegThree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/1a1044c0-c261-5b63-8407-715572ac7a6b
-- title:
--   A finite-order Hecke character of ℚ of modulus (3)
-- statement:
--   The assertion is the existence of a monoid homomorphism $\omega$ from the unit group of the adele ring of $\mathbb{Q}$ (formed over $\mathcal{O}_{\mathbb{Q}}$, as a product of the infinite adeles and the finite adeles) to $\mathbb{C}^{\times}$ with five properties. First, [`HeckeCharacter.IsFiniteOrderHeckeChar`](def/HeckeCharacter_FiniteOrder.html#L13) holds: $\omega$ is trivial on the image of $\mathbb{Q}^{\times}$ under the diagonal embedding, $\omega$ is continuous, and $\omega$ is of finite order. Second, $\omega$ admits the modulus $(3) =$ `Ideal.span {(3 : 𝓞 ℚ)}`, meaning that $\omega(u) = 1$ whenever the archimedean component of $u$ is $1$ and, at every finite place $v$, the component $u_v$ satisfies $v(u_v) = 1$ and $v(u_v - 1) \le \exp(-m_v)$, where $m_v$ is the multiplicity of $v$ in the factorisation of $(3)$ (so $m_v = 1$ for $v = (3)$ and $m_v = 0$ otherwise). Third, for every finite place $v$ with $v \neq (3)$, the value of $\omega$ on [`AutomorphicForm.uniformizerIdele ℚ v`](def/AutomorphicForm_HeckeEigenfunction.html#L31) — the idele with archimedean component $1$, component the chosen uniformiser of $v$ at $v$ and $1$ at all other finite places — equals the integer $\chi_{-3}(N v)$ viewed in $\mathbb{C}$, where $N v$ is the absolute norm of $v$ and $\chi_{-3}(n)$ is $1$ if $n \equiv 1 \pmod 3$, $-1$ if $n \equiv 2 \pmod 3$, and $0$ otherwise. Fourth, $\omega(u) = -1$ for every adelic unit $u$ whose archimedean component is $-1$ and whose finite component is $1$. Fifth, $\omega(u) = 1$ for every adelic unit $u$ whose archimedean component is $1$, whose finite component is $1$ at every place other than $(3)$, and whose component at $(3)$ is $3$.
--
--   This realises the quadratic Dirichlet character of conductor $3$ as an idele class character of $\mathbb{Q}$: a finite-order Hecke character of modulus $(3)$, odd at the archimedean place, whose Frobenius values away from $3$ are $\chi_{-3}$ of the residue degree and which is normalised to take the value $1$ on the uniformiser $3$ at the ramified place. It is used in the Langlands–Tunnell part of the development, where such a character supplies the central character data for the automorphic form attached to an octahedral or tetrahedral representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IdeleChar_exists_finiteOrderHeckeChar_chiNegThree.lean

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_ModularForm_EisensteinChiNegThree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.IdeleChar.exists_finiteOrderHeckeChar_chiNegThree :
    ∃ ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ,
      HeckeCharacter.IsFiniteOrderHeckeChar ℚ ω ∧
      HeckeCharacter.AdmitsModulus ℚ ω (Ideal.span {(3 : 𝓞 ℚ)}) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal ≠ Ideal.span {(3 : 𝓞 ℚ)} →
        ((ω (AutomorphicForm.uniformizerIdele ℚ v) : ℂˣ) : ℂ)
          = ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℂ)) ∧
      (∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
        (u : AdeleRing (𝓞 ℚ) ℚ).1 = -1 → (u : AdeleRing (𝓞 ℚ) ℚ).2 = 1 →
        ((ω u : ℂˣ) : ℂ) = -1) ∧
      (∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
        (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1 →
        (∀ w : HeightOneSpectrum (𝓞 ℚ), w.asIdeal ≠ Ideal.span {(3 : 𝓞 ℚ)} →
          ((u : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1) →
        (∀ w : HeightOneSpectrum (𝓞 ℚ), w.asIdeal = Ideal.span {(3 : 𝓞 ℚ)} →
          ((u : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) w = (3 : w.adicCompletion ℚ)) →
        ((ω u : ℂˣ) : ℂ) = 1) := by sorry
