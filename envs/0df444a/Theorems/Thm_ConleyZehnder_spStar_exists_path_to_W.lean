-- Prove2me | Theorems.Thm_ConleyZehnder_spStar_exists_path_to_W
-- name    : ConleyZehnder.spStar_exists_path_to_W
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T16:13:55.673992+00:00
-- url     : https://prove2.me/theorems/f05d67e7-d1c7-4251-97fb-06913abcbf0c
-- title:
--   Every matrix in $\mathrm{Sp}^*(2n)$ is joined to $W^+$ or $W^-$ inside $\mathrm{Sp}^*(2n)$
-- statement:
--   Let $\mathrm{Sp}^*(2n)$ be the set of real symplectic $2n\times 2n$ matrices $A$ (with respect to $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$) such that $1$ is not an eigenvalue of $A$, i.e. $\det(\mathrm{Id}-A)\neq 0$. Let $W^+=-\mathrm{Id}$ and $W^-=\mathrm{diag}(2,-1,\dots,-1,\tfrac12,-1,\dots,-1)$.
--
--   For every $A\in\mathrm{Sp}^*(2n)$ there is a continuous path $\chi:[0,1]\to\mathrm{Sp}^*(2n)$ with $\chi(0)=A$ and $\chi(1)\in\{W^+,W^-\}$.
--
--   This is the existence half of the definition of the Conley–Zehnder index: every $\psi\in\mathrm{SP}(n)$ admits an extension $\tilde\psi$ through $\mathrm{Sp}^*(2n)$ ending at $W^\pm$.
--
--   Formalization note: paths are `C(unitInterval, Mat n)`, where `Mat n` is the type of real matrices indexed by `Fin n ⊕ Fin n`; `SpStar n`, `Wplus n`, `Wminus n` are from the definition module `ConleyZehnder_Setting`. For $n=0$ the statement is trivial.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Section 2, the first of the two facts listed before Definition 7, p. 6; Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Gutt §2, first fact before Definition 7: every `A ∈ Sp*` is joined inside `Sp*` to
`W⁺` or to `W⁻`. -/
theorem spStar_exists_path_to_W {n : ℕ} (A : Mat n) (hA : A ∈ SpStar n) :
    ∃ χ : C(unitInterval, Mat n), χ 0 = A ∧ (∀ t, χ t ∈ SpStar n) ∧
      (χ 1 = Wplus n ∨ χ 1 = Wminus n) := by sorry

end ConleyZehnder
