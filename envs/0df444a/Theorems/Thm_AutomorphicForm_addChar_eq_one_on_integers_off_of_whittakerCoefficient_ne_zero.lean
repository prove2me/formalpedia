-- Prove2me | Theorems.Thm_AutomorphicForm_addChar_eq_one_on_integers_off_of_whittakerCoefficient_ne_zero
-- name    : AutomorphicForm.addChar_eq_one_on_integers_off_of_whittakerCoefficient_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/c9cec4a2-1262-513e-a34d-e571833199d5
-- title:
--   Non-vanishing Whittaker coefficient forces ψ unramified outside S
-- statement:
--   Let $F$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_F)$ and $G_0\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ a function satisfying: $G_0(n(\beta)h)=G_0(h)$ for every $\beta\in F$ and every $h$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\beta$ is viewed in $\mathbb{A}_F$; and, for a given finite set $S$ of maximal ideals of $\mathcal{O}_F$, $G_0(g\cdot \iota_v(k_v))=G_0(g)$ for every $v\notin S$, every $k_v\in\mathrm{GL}_2(\mathcal{O}_v)$ (mapped into $\mathrm{GL}_2(F_v)$) and every $g$, where $\iota_v$ places a matrix at the component $v$ and the identity at all other places. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ which is trivial on $F$, continuous and non-trivial. Let $g_0\in\mathrm{GL}_2(\mathbb{A}_F)$ have all entries agreeing at $v$ with those of the identity matrix for every $v\notin S$, and let $a_0\in\mathbb{A}_F^\times$ have $v$-component $1$ for every $v\notin S$. Assume the Whittaker coefficient at $\alpha=1$, namely $\int G_0(n(x)\,\mathrm{diag}(a_0,1)g_0)\,\psi(-x)\,d\nu(x)$ with $\nu$ the adelic additive Haar measure conditioned on the box consisting of adeles whose infinite part lies in the fundamental domain of the lattice basis and whose finite part is everywhere integral (the remaining data of the pins being $D$, the full central subgroup, the levels $\mathrm{levelOne}\sqcap\mathrm{finiteAdelicGL2Subgroup}$ and the Hecke generators `heckeGen`), is non-zero. Then for every $v\notin S$ and every $r\in\mathcal{O}_v$, the value of $\psi$ at the adele with zero infinite part and finite part equal to $r$ at $v$ and $0$ elsewhere is $1$.
--
--   This is the statement that the local components $\psi_v$ of a global additive character are unramified, i.e. trivial on $\mathcal{O}_v$, at every finite place outside the set $S$ where the function is spherical, deduced from non-vanishing of its first Whittaker coefficient at a point that is trivial off $S$. It feeds the construction of a non-vanishing zeta integrand used further on in the analytic input to the argument, via [`AutomorphicForm.whittakerCoefficient_unipotentGL2_mul`](thm.html#AutomorphicForm.whittakerCoefficient_unipotentGL2_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_addChar_eq_one_on_integers_off_of_whittakerCoefficient_ne_zero.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox MeasureTheory
open AutomorphicForm IsDedekindDomain UnramifiedWhittaker

theorem AutomorphicForm.addChar_eq_one_on_integers_off_of_whittakerCoefficient_ne_zero
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (G₀ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (β : F) (h : AdelicGL2 (𝓞 F) F), G₀ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * h) = G₀ h)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hKS : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers F)) (g : AdelicGL2 (𝓞 F) F),
        G₀ (g * placeEmbed F v
          (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) kv)) = G₀ g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ i j : Fin 2,
      ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
        ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v)
    (a₀ : (AdeleRing (𝓞 F) F)ˣ)
    (ha₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1)
    (hW : whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G₀ 1 (diagOne a₀ * g₀) ≠ 0) :
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ r : v.adicCompletionIntegers F,
      ψ (@id (AdeleRing (𝓞 F) F) ((0 : InfiniteAdeleRing F),
        AdelicDock.splice (𝓞 F) F v 0 (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r))) = 1 := by sorry
