-- Prove2me | Theorems.Thm_AutomorphicForm_even_sub_of_archOccursInClassOf_archWeightChar
-- name    : AutomorphicForm.even_sub_of_archOccursInClassOf_archWeightChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/c00ae15e-229c-5f18-a00f-48e19b76990d
-- title:
--   Parity of archimedean weights at a real place is constant
-- statement:
--   Let $F$ be a number field, let $D$ be an arbitrary subset of $\mathrm{GL}_2(\mathbb{A}_F)$ (the general linear group of $2\times 2$ matrices over the adele ring of $\mathcal{O}_F$ in $F$), let $\Theta$ be a complex Hecke eigensystem over $F$ — that is, a nonzero level ideal of $\mathcal{O}_F$ together with two families $a,b$ of complex numbers indexed by the height-one primes — and let $w$ be an infinite place of $F$ that is real, with $h_w$ a witness of this. Fix integers $n$ and $m$. For an integer $k$, consider the character of the relevant archimedean subgroup at $w$ obtained by transporting the weight-$k$ character `archWeightCharℝ` along the isomorphism $F_w\cong\mathbb{R}$ given by `ringEquivRealOfIsReal` (and its norm preservation) via `rowIsometrySubgroup₀Map`, and let $P_k(\varphi)$ be the assertion `HasArchCharacterAt₀` that $\varphi\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ transforms by this character at $w$. The hypotheses are that each of $P_n$ and $P_m$ occurs in the class of $\Theta$ on $D$, meaning: there is a Hecke eigensystem $\Theta'$ whose $a$- and $b$-tables agree with those of $\Theta$ outside some finite set of height-one primes, and a smooth cuspidal realization $R'$ at the production pins built from $D$ (Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, full central subgroup, level subgroups $N\mapsto \text{levelOne}(N)\cap \ker(\text{glArch})$, Hecke generators `heckeGen`, and the adelic-box conditioned measure) for the central renormalisation $\Theta'.\mathtt{toRawCentral}$ (same level and $a$, with $b_v$ scaled by $(\mathrm{cNorm}\,v)^{-1}$), such that the underlying function of $R'$ is continuous and satisfies $P_n$ (resp. $P_m$). The conclusion is that $n-m$ is even.
--
--   This is the statement that all $\mathrm{SO}(2)$-types occurring at a real place within one near-equivalence class of cuspidal Hecke eigensystems on $\mathrm{GL}_2$ have the same parity, the parity being read off from the value of the common central character at $-1$ placed at $w$. It is used in the analysis of $K$-types at real places, both in the characterisation of occurring types by archimedean lowering and in the Casimir/Laplace-eigenvalue bookkeeping of the Langlands–Tunnell step; the proof cites the constancy of the central character across eigensystems agreeing away from finitely many places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_even_sub_of_archOccursInClassOf_archWeightChar.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.even_sub_of_archOccursInClassOf_archWeightChar
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (Θ : HeckeEigensystem F ℂ)
    (w : InfinitePlace F) (hw : w.IsReal) (n m : ℤ)
    (hn : ArchOccursInClassOf F D Θ
      (fun φ => HasArchCharacterAt₀ F w
        ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
          (norm_ringEquivRealOfIsReal hw))) φ))
    (hm : ArchOccursInClassOf F D Θ
      (fun φ => HasArchCharacterAt₀ F w
        ((archWeightCharℝ m).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
          (norm_ringEquivRealOfIsReal hw))) φ)) :
    Even (n - m) := by sorry
